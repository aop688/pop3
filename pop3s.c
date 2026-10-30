/*
* pop3s.c — POP3S server (GnuTLS edition)
* sudo apt update && sudo apt install libgnutls30 libgnutls28-dev gnutls-bin
* gcc -O2 -o pop3s pop3s.c -lgnutls
* sudo setcap cap_net_bind_service=+ep pop3
* ps -eo pid,ppid,cmd,rss,vsz,pmem | grep pop3
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <errno.h>
#include <limits.h>
#include <stdint.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <time.h>
#include <stdarg.h>
#include <dirent.h>
#include <sys/epoll.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <gnutls/gnutls.h>
#include <gnutls/crypto.h>

#define PORT                   995
#define CERT                   "server.crt"
#define KEY                    "server.key"
#define MAILDIR                "/var/mail/inbox"
#define USER                   "POPUSER"
#define PASS                   "PASSWORD"
#define MAX_LINE               1024
#define INIT_MSG_CAPACITY      16
#define SESSION_TIMEOUT_SEC    60
#define HANDSHAKE_TIMEOUT_SEC  10
#define MAX_MAIL_SIZE          (50 * 1024 * 1024)
#define MAX_SENDQ_BYTES        (1024 * 1024)
#define STREAM_CHUNK           8192
#define SEND_BUDGET            (256 * 1024)
#define MAX_PENDING_RETR       4

#define MAX_ARGS               1
#define MAX_AUTH_FAILS         3
#define MAX_BAD_CMDS           2

#define LOG(fmt, ...) do { \
    struct timespec _ts; \
    struct tm _tm; \
    clock_gettime(CLOCK_REALTIME, &_ts); \
    localtime_r(&_ts.tv_sec, &_tm); \
    fprintf(stderr, "%02d:%02d:%02d.%03ld " fmt "\n", \
            _tm.tm_hour, _tm.tm_min, _tm.tm_sec, \
            _ts.tv_nsec / 1000000L, ##__VA_ARGS__); \
} while (0)

enum { STATE_AUTH, STATE_TRANSACTION };

enum { CONN_HANDSHAKE, CONN_RUNNING, CONN_CLOSING };

enum cmd_result {
    CMD_OK    =  0,   /* 继续会话 */
    CMD_QUIT  =  1,   /* 正常结束：flush 后关闭 */
    CMD_FATAL = -1,   /* 异常：flush 后关闭 */
};

struct mail {
    char *path;
    off_t size;
    int del;
};

struct sendq_node {
    char *data;
    size_t size;
    size_t sent;
    int stream;
    int fd;
    int line_start;
    int prev_cr;
    struct sendq_node *next;
};

struct session {
    int fd;
    gnutls_session_t tls;
    int phase;
    int state;
    time_t expire_at;
    char cip[INET_ADDRSTRLEN];
    char user_tmp[64];
    int auth_fails;
    int bad_cmds;

    struct mail *msgs;
    size_t msg_size;
    size_t msg_cap;

    char rbuf[256];
    size_t rlen;

    struct sendq_node *send_head;
    struct sendq_node *send_tail;
    size_t sendq_bytes;
    size_t pending_streams;

    struct session * next;
};

struct server {
    gnutls_certificate_credentials_t tls_creds;
    gnutls_priority_t tls_prio;
    int epoll_fd;
    int server_fd;
    struct session * cons;
};

static volatile sig_atomic_t g_run;

static void node_free(struct sendq_node *n) {
    if (n->fd >= 0) close(n->fd);
    free(n->data);
    free(n);
}

static void sendq_free(struct session *conn) {
    struct sendq_node *n = conn->send_head;
    while (n) {
        struct sendq_node *next = n->next;
        node_free(n);
        n = next;
    }
    conn->send_head = conn->send_tail = NULL;
    conn->sendq_bytes = 0;
    conn->pending_streams = 0;
}

static void conn_free(struct server *srv, struct session *conn) {
    struct session **pp = &srv->cons;
    while (*pp && *pp != conn) {
        pp = &(*pp)->next;
    }
    if (*pp) {
        *pp = conn->next;
    }

    epoll_ctl(srv->epoll_fd, EPOLL_CTL_DEL, conn->fd, NULL);

    if (conn->tls) {
        if (conn->phase != CONN_HANDSHAKE) {
            gnutls_bye(conn->tls, GNUTLS_SHUT_WR);
        }
        gnutls_deinit(conn->tls);
    }
    close(conn->fd);

    for (size_t i = 0; i < conn->msg_size; i++) {
        free(conn->msgs[i].path);
    }
    free(conn->msgs);
    sendq_free(conn);
    free(conn);
}

static void sendq_append(struct session *conn, struct sendq_node *node) {
    node->next = NULL;
    if (conn->send_tail) {
        conn->send_tail->next = node;
    } else {
        conn->send_head = node;
    }
    conn->send_tail = node;
}

static int sendq_attach(struct session *conn, char *data, size_t len) {
    struct sendq_node *node = calloc(1, sizeof(*node));
    if (!node) return -1;
    node->data = data;
    node->size = len;
    node->fd = -1;
    sendq_append(conn, node);
    conn->sendq_bytes += len;
    return 0;
}

static int sendq_busy(const struct session *conn) {
    return conn->sendq_bytes > MAX_SENDQ_BYTES || conn->pending_streams >= MAX_PENDING_RETR;
}

static struct sendq_node *stream_node_new(int fd) {
    struct sendq_node *node = calloc(1, sizeof(*node));
    if (!node) return NULL;
    node->data = malloc(2 * STREAM_CHUNK + 8);
    if (!node->data) {
        free(node);
        return NULL;
    }
    node->stream = 1;
    node->fd = -1;
    node->line_start = 1;
    node->prev_cr = 0;
    node->fd = fd;
    return node;
}

static int stream_refill(struct sendq_node *n) {
    char raw[STREAM_CHUNK];
    ssize_t r;
    do {
        r = read(n->fd, raw, sizeof(raw));
    } while (r < 0 && errno == EINTR);
    if (r < 0) {
        LOG("read mail: %s", strerror(errno));
        return -1;
    }

    char *wp = n->data;
    if (r == 0) {
        if (!n->line_start) {
            if (!n->prev_cr) *wp++ = '\r';
            *wp++ = '\n';
        }
        *wp++ = '.'; *wp++ = '\r'; *wp++ = '\n';
        close(n->fd);
        n->fd = -1;
    } else {
        for (ssize_t i = 0; i < r; i++) {
            char c = raw[i];
            if (c == '\n') {
                if (!n->prev_cr) *wp++ = '\r';
                *wp++ = '\n';
                n->line_start = 1;
                n->prev_cr = 0;
                continue;
            }
            if (n->line_start && c == '.') *wp++ = '.';
            *wp++ = c;
            n->line_start = 0;
            n->prev_cr = (c == '\r');
        }
    }
    n->size = (size_t)(wp - n->data);
    n->sent = 0;
    return 0;
}

static int conn_send(struct session *conn, const char *fmt, ...) {
    char *buf = malloc(MAX_LINE);
    if (!buf) return -1;
    va_list ap;
    va_start(ap, fmt);
    int len = vsnprintf(buf, MAX_LINE - 2, fmt, ap);
    va_end(ap);
    if (len < 0) {
        free(buf);
        return -1;
    }
    if (len >= MAX_LINE - 2) len = MAX_LINE - 3;
    buf[len] = '\r';
    buf[len + 1] = '\n';
    LOG("S: %.*s", len, buf);
    if (sendq_attach(conn, buf, (size_t)len + 2) < 0) {
        free(buf);
        return -1;
    }
    return 0;
}

static void new_to_cur(void) {
    DIR *dir = opendir(MAILDIR "/new");
    if (!dir) return;

    struct dirent *entry;
    while ((entry = readdir(dir))) {
        if (entry->d_name[0] == '.') continue;

        char src[MAX_LINE], dst[MAX_LINE];
        int slen = snprintf(src, sizeof(src), MAILDIR"/new/%s", entry->d_name);
        int dlen = snprintf(dst, sizeof(dst), MAILDIR"/cur/%s", entry->d_name);
        if (slen >= MAX_LINE || dlen >= MAX_LINE) continue;

        struct stat st;
        if (stat(src, &st) != 0 || !S_ISREG(st.st_mode)) continue;

        if (rename(src, dst) != 0) {
            LOG("rename '%s' -> '%s': %s", src, dst, strerror(errno));
        } else {
            LOG("moved '%s' -> '%s'", src, dst);
        }
    }
    closedir(dir);
}

static size_t load_mailbox(struct session *conn, const char *dirpath) {
    for (size_t i = 0; i < conn->msg_size; i++) {
        free(conn->msgs[i].path);
        conn->msgs[i].path = NULL;
    }
    conn->msg_size = 0;

    if (conn->msg_cap < INIT_MSG_CAPACITY) {
        struct mail *tmp = realloc(conn->msgs, INIT_MSG_CAPACITY * sizeof(struct mail));
        if (!tmp) return 0;
        conn->msgs = tmp;
        conn->msg_cap = INIT_MSG_CAPACITY;
    }

    new_to_cur();

    DIR *dir = opendir(dirpath);
    if (!dir) {
        return 0;
    }
    struct dirent *entry;
    while ((entry = readdir(dir))) {
        if (entry->d_name[0] == '.') continue;

        char filepath[MAX_LINE];
        int fplen = snprintf(filepath, sizeof(filepath), "%s/%s", dirpath, entry->d_name);
        if (fplen >= MAX_LINE) continue;

        struct stat st;
        if (stat(filepath, &st) != 0 || !S_ISREG(st.st_mode)) continue;

        if (st.st_size <= 0 || st.st_size > MAX_MAIL_SIZE) {
            LOG("MAILBOX skip bad-size file: %s (%lld bytes)",
                filepath, (long long)st.st_size);
            continue;
        }

        if (conn->msg_size == conn->msg_cap) {
            size_t new_cap = conn->msg_cap * 2;
            struct mail *tmp = realloc(conn->msgs, new_cap * sizeof(struct mail));
            if (!tmp) continue;
            conn->msgs = tmp;
            conn->msg_cap = new_cap;
        }

        struct mail *msg = &conn->msgs[conn->msg_size];
        msg->path = strdup(filepath);
        if (!msg->path) continue;
        msg->size = st.st_size;
        msg->del = 0;
        conn->msg_size++;
    }
    closedir(dir);
    return conn->msg_size;
}

static int auth_userpass(const char *user, const char *password) {
    size_t ulen = strlen(USER);
    size_t plen = strlen(PASS);
    int user_ok = (strlen(user) == ulen) ? (gnutls_memcmp(user, USER, ulen) == 0) : 0;
    int pass_ok = (strlen(password) == plen) ? (gnutls_memcmp(password, PASS, plen) == 0) : 0;
    return user_ok & pass_ok;
}

static int parse_uint(const char *s, int *out) {
    if (!s || !*s) return -1;
    errno = 0;
    char *end;
    long v = strtol(s, &end, 10);
    if (errno || *end != '\0' || v < 0 || v > INT_MAX) return -1;
    *out = (int)v;
    return 0;
}

static int parse_msgno(const char *s, int *out) {
    int n;
    if (parse_uint(s, &n) < 0 || n < 1) return -1;
    *out = n;
    return 0;
}

static int msg_valid(const struct session *conn, int n) {
    return n >= 1 && (size_t)n <= conn->msg_size && !conn->msgs[n - 1].del;
}

static void msg_uid(const char *path, char out[33]) {
    unsigned char digest[16];
    const char *slash = strrchr(path, '/');
    const char *fname = slash ? slash + 1 : path;
    const char *colon = strchr(fname, ':');
    size_t len = colon ? (size_t)(colon - fname) : strlen(fname);

    int ret = gnutls_hash_fast(GNUTLS_DIG_MD5, fname, len, digest);
    if (ret < 0) {
        LOG("msg_uid: %s", gnutls_strerror(ret));
        snprintf(out, 33, "%032d", 0);
        return;
    }
    for (int k = 0; k < 16; k++) {
        snprintf(out + k * 2, 3, "%02x", digest[k]);
    }
}

static int cmd_capa(struct session *c, int argc, char **argv) {
    conn_send(c, "+OK Capability list follows");
    conn_send(c, "UIDL");
    if (c->state == STATE_AUTH)
        conn_send(c, "USER");
    conn_send(c, "RESP-CODES");
    conn_send(c, ".");
    return CMD_OK;
}

static int cmd_noop(struct session *c, int argc, char **argv) {
    conn_send(c, "+OK");
    return CMD_OK;
}

static int cmd_quit(struct session *c, int argc, char **argv) {
    if (c->state == STATE_TRANSACTION) {
        for (size_t i = 0; i < c->msg_size; i++) {
            struct mail *m = &c->msgs[i];
            if (!m->del) continue;
            if (unlink(m->path) != 0) {
                LOG("unlink '%s': %s", m->path, strerror(errno));
            }
        }
    }
    conn_send(c, "+OK bye");
    return CMD_QUIT;
}

static int cmd_user(struct session *c, int argc, char **argv) {
    if (strlen(argv[0]) >= sizeof(c->user_tmp)) {
        conn_send(c, "-ERR auth");
        return CMD_OK;
    }
    snprintf(c->user_tmp, sizeof(c->user_tmp), "%s", argv[0]);
    conn_send(c, "+OK");
    return CMD_OK;
}

static int cmd_pass(struct session *c, int argc, char **argv) {
    if (!c->user_tmp[0]) {
        conn_send(c, "-ERR auth");
        return CMD_OK;
    }
    int ok = auth_userpass(c->user_tmp, argv[0]);
    memset(c->user_tmp, 0, sizeof(c->user_tmp));

    if (ok) {
        c->auth_fails = 0;
        load_mailbox(c, MAILDIR"/cur");
        c->state = STATE_TRANSACTION;
        conn_send(c, "+OK");
        return CMD_OK;
    }
    c->auth_fails++;
    LOG("AUTH FAIL %s (%d/%d)", c->cip, c->auth_fails, MAX_AUTH_FAILS);
    conn_send(c, "-ERR auth");
    return c->auth_fails >= MAX_AUTH_FAILS ? CMD_QUIT : CMD_OK;
}

static int cmd_stat(struct session *c, int argc, char **argv) {
    off_t total = 0;
    int count = 0;
    for (size_t i = 0; i < c->msg_size; i++) {
        if (c->msgs[i].del) continue;
        count++;
        total += c->msgs[i].size;
    }
    conn_send(c, "+OK %d %lld", count, (long long)total);
    return CMD_OK;
}

static int cmd_list(struct session *c, int argc, char **argv) {
    if (argc == 1) {
        int n;
        if (parse_msgno(argv[0], &n) < 0 || !msg_valid(c, n)) {
            conn_send(c, "-ERR no such message");
            return CMD_OK;
        }
        conn_send(c, "+OK %d %lld", n, (long long)c->msgs[n - 1].size);
        return CMD_OK;
    }
    off_t total = 0;
    int count = 0;
    for (size_t i = 0; i < c->msg_size; i++) {
        if (c->msgs[i].del) continue;
        count++;
        total += c->msgs[i].size;
    }
    conn_send(c, "+OK %d messages (%lld octets)", count, (long long)total);
    for (size_t i = 0; i < c->msg_size; i++) {
        if (c->msgs[i].del) continue;
        conn_send(c, "%zu %lld", i + 1, (long long)c->msgs[i].size);
    }
    conn_send(c, ".");
    return CMD_OK;
}

static int cmd_uidl(struct session *c, int argc, char **argv) {
    char uid[33];
    if (argc == 1) {
        int n;
        if (parse_msgno(argv[0], &n) < 0 || !msg_valid(c, n)) {
            conn_send(c, "-ERR no such message");
            return CMD_OK;
        }
        msg_uid(c->msgs[n - 1].path, uid);
        conn_send(c, "+OK %d %s", n, uid);
        return CMD_OK;
    }
    conn_send(c, "+OK");
    for (size_t i = 0; i < c->msg_size; i++) {
        if (c->msgs[i].del) continue;
        msg_uid(c->msgs[i].path, uid);
        conn_send(c, "%zu %s", i + 1, uid);
    }
    conn_send(c, ".");
    return CMD_OK;
}

static int cmd_retr(struct session *c, int argc, char **argv) {
    int n;
    if (parse_msgno(argv[0], &n) < 0) {
        conn_send(c, "-ERR invalid argument");
        return CMD_OK;
    }
    if (!msg_valid(c, n)) {
        conn_send(c, "-ERR no such message");
        return CMD_OK;
    }
    if (sendq_busy(c)) {
        conn_send(c, "-ERR busy");
        return CMD_OK;
    }

    const char *path = c->msgs[n - 1].path;
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) {
        LOG("open '%s': %s", path, strerror(errno));
        conn_send(c, "-ERR sys");
        return CMD_OK;
    }
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) ||
        st.st_size <= 0 || st.st_size > MAX_MAIL_SIZE) {
        close(fd);
        conn_send(c, "-ERR sys");
        return CMD_OK;
    }

    struct sendq_node *node = stream_node_new(fd);
    if (!node) {
        close(fd);
        conn_send(c, "-ERR sys");
        return CMD_OK;
    }
    if (conn_send(c, "+OK %lld octets", (long long)st.st_size) < 0) {
        node_free(node);
        return CMD_FATAL;
    }
    sendq_append(c, node);
    c->pending_streams++;
    return CMD_OK;
}

static int cmd_dele(struct session *c, int argc, char **argv) {
    int n;
    if (parse_msgno(argv[0], &n) < 0 || !msg_valid(c, n)) {
        conn_send(c, "-ERR no such message");
        return CMD_OK;
    }
    c->msgs[n - 1].del = 1;
    conn_send(c, "+OK message %d deleted", n);
    return CMD_OK;
}

#define ST_AUTH   (1u << STATE_AUTH)
#define ST_TRANS  (1u << STATE_TRANSACTION)
#define ST_ANY    (ST_AUTH | ST_TRANS)

typedef int (*cmd_fn)(struct session *conn, int argc, char **argv);

struct pop3_cmd {
    const char *name;
    unsigned    states;
    int         min_args;
    int         max_args;
    int         raw_arg;
    int         sensitive;
    cmd_fn      func;
};

static const struct pop3_cmd pop3_cmds[] = {
    /* name    states    min max raw sens func */
    { "CAPA",  ST_ANY,   0, 0,  0,  0,   cmd_capa },
    { "NOOP",  ST_ANY,   0, 0,  0,  0,   cmd_noop },
    { "QUIT",  ST_ANY,   0, 0,  0,  0,   cmd_quit },
    { "USER",  ST_AUTH,  1, 1,  1,  0,   cmd_user },
    { "PASS",  ST_AUTH,  1, 1,  1,  1,   cmd_pass },
    { "STAT",  ST_TRANS, 0, 0,  0,  0,   cmd_stat },
    { "LIST",  ST_TRANS, 0, 1,  0,  0,   cmd_list },
    { "UIDL",  ST_TRANS, 0, 1,  0,  0,   cmd_uidl },
    { "RETR",  ST_TRANS, 1, 1,  0,  0,   cmd_retr },
    { "DELE",  ST_TRANS, 1, 1,  0,  0,   cmd_dele },
};

static const struct pop3_cmd *find_cmd(const char *name) {
    for (size_t i = 0; i < sizeof(pop3_cmds) / sizeof(*pop3_cmds); i++)
        if (strcasecmp(pop3_cmds[i].name, name) == 0)
            return &pop3_cmds[i];
    return NULL;
}

static int split_args(char *s, char **argv, int max) {
    int n = 0;
    while (*s) {
        while (*s == ' ' || *s == '\t') s++;
        if (!*s) break;
        if (n == max) return -1;
        argv[n++] = s;
        while (*s && *s != ' ' && *s != '\t') s++;
        if (*s) *s++ = '\0';
    }
    return n;
}

static int bad_command(struct session *c, const char *msg) {
    conn_send(c, "-ERR %s", msg);
    return ++c->bad_cmds >= MAX_BAD_CMDS ? CMD_FATAL : CMD_OK;
}

static int dispatch_pop3_cmd(struct session *c, char *line) {
    char *p = line;
    while (*p == ' ' || *p == '\t') p++;
    if (!*p) {
        LOG("C: <empty>");
        return bad_command(c, "empty command");
    }
    char *cmd = p;
    while (*p && *p != ' ' && *p != '\t') p++;
    if (*p) *p++ = '\0';
    char *rest = p;

    const struct pop3_cmd *cm = find_cmd(cmd);

    if (cm && cm->sensitive)
        LOG("C: %s ********", cmd);
    else if (*rest)
        LOG("C: %s %s", cmd, rest);
    else
        LOG("C: %s", cmd);

    if (!cm)
        return bad_command(c, "unknown command");
    if (!(cm->states & (1u << c->state))) {
        conn_send(c, "-ERR command not allowed in this state");
        return CMD_OK;
    }

    char *argv[MAX_ARGS] = { NULL };
    int argc;
    if (cm->raw_arg) {
        argc = *rest ? 1 : 0;
        argv[0] = rest;
    } else {
        argc = split_args(rest, argv, MAX_ARGS);
        if (argc < 0) {
            conn_send(c, "-ERR too many arguments");
            return CMD_OK;
        }
    }
    if (argc < cm->min_args || argc > cm->max_args) {
        conn_send(c, "-ERR wrong number of arguments");
        return CMD_OK;
    }
    return cm->func(c, argc, argv);
}

static int feed_input(struct session *conn, const char *data, size_t len) {
    while (len > 0) {
        const char *nl = memchr(data, '\n', len);
        size_t chunk = nl ? (size_t)(nl - data) : len;

        if (chunk >= sizeof(conn->rbuf) - conn->rlen) {
            conn_send(conn, "-ERR line too long");
            return CMD_FATAL;
        }
        memcpy(conn->rbuf + conn->rlen, data, chunk);
        conn->rlen += chunk;

        if (!nl) break;

        data += chunk + 1;
        len -= chunk + 1;

        if (conn->rlen > 0 && conn->rbuf[conn->rlen - 1] == '\r')
            conn->rlen--;
        conn->rbuf[conn->rlen] = '\0';
        conn->rlen = 0;
        int r = dispatch_pop3_cmd(conn, conn->rbuf);
        if (r != CMD_OK)
            return r;
    }
    return CMD_OK;
}

static void epoll_mod(struct server *srv, struct session *conn, uint32_t events) {
    struct epoll_event ev;
    memset(&ev, 0, sizeof(ev));
    ev.events = events;
    ev.data.ptr = conn;
    epoll_ctl(srv->epoll_fd, EPOLL_CTL_MOD, conn->fd, &ev);
}

static int process_read(struct session *conn) {
    char tmp[4096];
    do {
        ssize_t n = gnutls_record_recv(conn->tls, tmp, sizeof(tmp));
        if (n == GNUTLS_E_AGAIN || n == GNUTLS_E_INTERRUPTED) {
            return CMD_OK;
        }
        if (n <= 0) {
            return CMD_FATAL;
        }
        conn->expire_at = time(NULL) + SESSION_TIMEOUT_SEC;
        int r = feed_input(conn, tmp, (size_t)n);
        memset(tmp, 0, sizeof(tmp));
        if (r != CMD_OK)
            return r;
    } while (gnutls_record_check_pending(conn->tls) > 0);
    return CMD_OK;
}

static int sendq_flush(struct session *conn) {
    size_t budget = SEND_BUDGET;

    while (conn->send_head) {
        struct sendq_node *node = conn->send_head;

        if (node->sent == node->size) {
            if (node->fd >= 0) {
                if (stream_refill(node) < 0) return -1;
                continue;
            }
            conn->send_head = node->next;
            if (!conn->send_head) conn->send_tail = NULL;
            if (node->stream) conn->pending_streams--;
            node_free(node);
            continue;
        }

        if (budget == 0) return 1;

        const char *ptr = node->data + node->sent;
        size_t rem = node->size - node->sent;

        ssize_t n = gnutls_record_send(conn->tls, ptr, rem);
        if (n > 0) {
            node->sent += (size_t)n;
            if (!node->stream) conn->sendq_bytes -= (size_t)n;
            budget = (size_t)n >= budget ? 0 : budget - (size_t)n;
            continue;
        }
        if (n == GNUTLS_E_AGAIN || n == GNUTLS_E_INTERRUPTED) {
            return 1;
        }
        return -1;
    }
    return 0;
}

static void handle_handshake(struct server *srv, struct session *conn) {
    int ret = gnutls_handshake(conn->tls);
    if (ret == GNUTLS_E_SUCCESS) {
        LOG("+ %s fd=%d tls=%s", conn->cip, conn->fd, gnutls_protocol_get_name(gnutls_protocol_get_version(conn->tls)));
        conn->phase = CONN_RUNNING;
        conn->expire_at = time(NULL) + SESSION_TIMEOUT_SEC;
        conn_send(conn, "+OK POP3 server ready");
        int fr = sendq_flush(conn);
        if (fr < 0) {
            conn_free(srv, conn);
            return;
        }
        epoll_mod(srv, conn, fr > 0 ? (EPOLLIN | EPOLLOUT) : EPOLLIN);
        return;
    }

    if (gnutls_error_is_fatal(ret)) {
        LOG("handshake fatal %s: %s", conn->cip, gnutls_strerror(ret));
        conn_free(srv, conn);
        return;
    }

    int dir = gnutls_record_get_direction(conn->tls);
    epoll_mod(srv, conn, dir ? EPOLLOUT : EPOLLIN);
}

static void handle_conn_io(struct server *srv, struct session *conn, uint32_t events) {
    if (events & EPOLLERR) {
        conn_free(srv, conn);
        return;
    }
    if (events & EPOLLOUT) {
        int r = sendq_flush(conn);
        if (r < 0) {
            conn_free(srv, conn);
            return;
        }
        if (r == 0 && conn->phase == CONN_CLOSING) {
            conn_free(srv, conn);
            return;
        }
    }
    if ((events & (EPOLLIN | EPOLLHUP)) && conn->phase == CONN_RUNNING) {
        int r = process_read(conn);
        if (r != CMD_OK) {
            conn->phase = CONN_CLOSING;
            int fr = sendq_flush(conn);
            if (fr < 0 || (fr == 0 && !conn->send_head)) {
                conn_free(srv, conn);
                return;
            }
            epoll_mod(srv, conn, EPOLLOUT);
            return;
        }
    }
    if (conn->phase == CONN_CLOSING) {
        if (conn->send_head)
            epoll_mod(srv, conn, EPOLLOUT);
        else
            conn_free(srv, conn);
        return;
    }
    epoll_mod(srv, conn, conn->send_head ? (EPOLLIN | EPOLLOUT) : EPOLLIN);
}

static void check_timeouts(struct server *srv) {
    time_t now = time(NULL);
    struct session *cur = srv->cons;
    while (cur) {
        struct session *next = cur->next;
        if (now >= cur->expire_at) {
            LOG("TIMEOUT %s %s", cur->cip, cur->phase == CONN_HANDSHAKE ? "handshake" : "session");
            conn_free(srv, cur);
        }
        cur = next;
    }
}

static int create_tls_context(struct server *srv, const char *cert, const char *key) {
    int ret = gnutls_certificate_allocate_credentials(&srv->tls_creds);
    if (ret < 0) {
        return -1;
    }
    ret = gnutls_certificate_set_x509_key_file(srv->tls_creds, cert, key,
                                               GNUTLS_X509_FMT_PEM);
    if (ret < 0) {
        fprintf(stderr, "load cert/key failed: %s\n", gnutls_strerror(ret));
        gnutls_certificate_free_credentials(srv->tls_creds);
        return -1;
    }
    ret = gnutls_priority_init(&srv->tls_prio, "NORMAL", NULL);
    if (ret < 0) {
        gnutls_certificate_free_credentials(srv->tls_creds);
        return -1;
    }
    gnutls_certificate_set_known_dh_params(srv->tls_creds, GNUTLS_SEC_PARAM_MEDIUM);
    return 0;
}

static void set_nonblock(int fd) {
    int flags = fcntl(fd, F_GETFL, 0);
    fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}

static int create_server(int port) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) {
        perror("socket");
        return -1;
    }
    int reuse = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &reuse, sizeof(reuse));
    set_nonblock(fd);
    struct sockaddr_in addr = {
        .sin_family = AF_INET,
        .sin_port = htons((uint16_t)port),
        .sin_addr.s_addr = INADDR_ANY,
    };
    if (bind(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        perror("bind");
        close(fd);
        return -1;
    }
    if (listen(fd, 128) < 0) {
        perror("listen");
        close(fd);
        return -1;
    }
    return fd;
}

static int create_epoll(struct server *srv) {
    int epfd = epoll_create1(0);
    if (epfd < 0) {
        perror("epoll_create1");
        return -1;
    }
    struct epoll_event ev = { .events = EPOLLIN, .data.ptr = NULL };
    epoll_ctl(epfd, EPOLL_CTL_ADD, srv->server_fd, &ev);
    return epfd;
}

static struct session *conn_new(struct server *srv, int cfd, gnutls_session_t tls) {
    struct session *conn = calloc(1, sizeof(*conn));
    if (!conn) {
        return NULL;
    }
    conn->fd = cfd;
    conn->tls = tls;
    conn->phase = CONN_HANDSHAKE;
    conn->expire_at = time(NULL) + HANDSHAKE_TIMEOUT_SEC;
    conn->state = STATE_AUTH;
    conn->next = srv->cons;
    srv->cons = conn;
    return conn;
}

static void accept_new_connections(struct server *srv) {
    for (;;) {
        struct sockaddr_in addr;
        socklen_t len = sizeof(addr);
        int cfd = accept(srv->server_fd, (struct sockaddr *)&addr, &len);
        if (cfd < 0) {
            if (errno == EAGAIN || errno == EWOULDBLOCK)
                break;
            if (errno == EINTR || errno == ECONNABORTED)
                continue;
            perror("accept");
            break;
        }
        set_nonblock(cfd);

        gnutls_session_t tls;
        int ret = gnutls_init(&tls, GNUTLS_SERVER | GNUTLS_NONBLOCK);
        if (ret < 0) {
            close(cfd);
            continue;
        }

        gnutls_priority_set(tls, srv->tls_prio);
        gnutls_credentials_set(tls, GNUTLS_CRD_CERTIFICATE, srv->tls_creds);
        gnutls_transport_set_int(tls, cfd);
        gnutls_certificate_server_set_request(tls, GNUTLS_CERT_IGNORE);

        struct session *conn = conn_new(srv, cfd, tls);
        if (!conn) {
            gnutls_deinit(tls);
            close(cfd);
            continue;
        }
        inet_ntop(AF_INET, &addr.sin_addr, conn->cip, sizeof(conn->cip));
        struct epoll_event ev = { .events = EPOLLIN, .data.ptr = conn };
        epoll_ctl(srv->epoll_fd, EPOLL_CTL_ADD, cfd, &ev);
    }
}

static void dispatch_event(struct server *srv, struct epoll_event *ev) {
    struct session *conn = ev->data.ptr;
    if (!conn)
        accept_new_connections(srv);
    else if (conn->phase == CONN_HANDSHAKE)
        handle_handshake(srv, conn);
    else
        handle_conn_io(srv, conn, ev->events);
}

static void run_event_loop(struct server *srv) {
    struct epoll_event events[64];
    time_t last_check = time(NULL);
    while (g_run) {
        int nfds = epoll_wait(srv->epoll_fd, events, 64, 1000);
        if (nfds < 0) {
            if (errno == EINTR) continue;
            perror("epoll_wait");
            break;
        }
        for (int i = 0; i < nfds; i++) {
            dispatch_event(srv, &events[i]);
        }
        time_t now = time(NULL);
        if (now - last_check >= 1) {
            check_timeouts(srv);
            last_check = now;
        }
    }
}

static void cleanup(struct server *srv) {
    while (srv->cons) {
        conn_free(srv, srv->cons);
    }
    if (srv->server_fd >= 0) close(srv->server_fd);
    if (srv->epoll_fd >= 0)  close(srv->epoll_fd);
    gnutls_priority_deinit(srv->tls_prio);
    gnutls_certificate_free_credentials(srv->tls_creds);
    gnutls_global_deinit();
}

static void signal_handler(int sig) {
    g_run = 0;
}

int main(int argc, char *argv[]) {
    int port = (argc > 1) ? atoi(argv[1]) : PORT;

    struct server srv = { .epoll_fd = -1, .server_fd = -1, };
    g_run = 1;
    gnutls_global_init();
    signal(SIGPIPE, SIG_IGN);
    signal(SIGINT, signal_handler);
    signal(SIGTERM, signal_handler);

    if (create_tls_context(&srv, CERT, KEY) < 0) {
        gnutls_global_deinit();
        return EXIT_FAILURE;
    }
    srv.server_fd = create_server(port);
    if (srv.server_fd < 0) {
        cleanup(&srv);
        return EXIT_FAILURE;
    }
    srv.epoll_fd = create_epoll(&srv);
    if (srv.epoll_fd < 0) {
        cleanup(&srv);
        return EXIT_FAILURE;
    }
    printf("pop3s %d\n", port);
    run_event_loop(&srv);
    cleanup(&srv);
    return EXIT_SUCCESS;
}
