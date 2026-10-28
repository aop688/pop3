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
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <time.h>
#include <stdarg.h>
#include <ctype.h>
#include <dirent.h>
#include <sys/epoll.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <gnutls/gnutls.h>
#include <gnutls/crypto.h>

#define PORT                995
#define CERT                "server.crt"
#define KEY                 "server.key"
#define MAILDIR             "/var/mail/inbox"
#define USER                "POPUSER"
#define PASS                "PASSWORD"
#define MAX_EVENTS          64
#define MAX_LINE            1024
#define INIT_MSG_CAPACITY   16
#define SESSION_TIMEOUT_SEC    60
#define HANDSHAKE_TIMEOUT_SEC  10
#define RBUF_INIT           512
#define MAX_MAIL_SIZE (50 * 1024 * 1024)

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

struct mail {
    char *path;
    off_t size;
    int del;
};

struct sendq_node {
    char *data;
    size_t size;
    size_t sent;
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
    struct mail * msgs;
    size_t msg_size;
    size_t msg_cap;

    char * rbuf;
    size_t rbuf_cap;
    size_t rlen;

    struct sendq_node *send_head;
    struct sendq_node *send_tail;

    struct session * next;
};

struct server {
    gnutls_certificate_credentials_t tls_creds;
    gnutls_priority_t tls_prio;
    int epoll_fd;
    int server_fd;
    struct session * cons;
};

static volatile int g_run;

static void sendq_free(struct session *conn) {
    struct sendq_node *n = conn->send_head;
    while (n) {
        struct sendq_node *next = n->next;
        free(n->data);
        free(n);
        n = next;
    }
    conn->send_head = conn->send_tail = NULL;
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

    for (int i = 0; i < (int)conn->msg_size; i++) {
        free(conn->msgs[i].path);
    }
    free(conn->msgs);
    free(conn->rbuf);
    sendq_free(conn);
    free(conn);
}

static int sendq_attach(struct session *conn, char *data, size_t len) {
    struct sendq_node *node = malloc(sizeof(struct sendq_node));
    if (!node) return -1;
    node->data  = data;
    node->size  = len;
    node->sent  = 0;
    node->next  = NULL;

    if (conn->send_tail) {
        conn->send_tail->next = node;
    } else {
        conn->send_head = node;
    }
    conn->send_tail = node;
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
    if (len >= MAX_LINE - 2) len = MAX_LINE - 2;
    buf[len] = '\r';
    buf[len + 1] = '\n';
    LOG("S: %.*s", len, buf);
    if (sendq_attach(conn, buf, len + 2) < 0) {
        free(buf);
        return -1;
    }
    return 0;
}

static void new_to_cur() {
    DIR *dir = opendir(MAILDIR"/new");
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

static size_t load_mailbox(struct session * conn, char * dirpath) {
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
    struct dirent * entry;
    while ((entry = readdir(dir))) {
        if (entry->d_name[0] == '.') continue;

        char filepath[MAX_LINE];
        int fplen = snprintf(filepath, sizeof(filepath), "%s/%s", dirpath, entry->d_name);
        if (fplen >= MAX_LINE) continue;

        struct stat st;
        if (stat(filepath, &st) != 0 || !S_ISREG(st.st_mode)) continue;

        if (st.st_size <= 0 || st.st_size > MAX_MAIL_SIZE) {
            LOG("MAILBOX skip oversized file: %s (%lld bytes)",
            filepath, (long long)st.st_size);
            continue;
        }

        if (conn->msg_size == conn->msg_cap) {
            size_t new_cap = conn->msg_cap * 2;
            struct mail * tmp = realloc(conn->msgs, new_cap * sizeof(struct mail));
            if (!tmp) continue;
            conn->msgs = tmp;
            conn->msg_cap = new_cap;
        }

        struct mail * msg = &conn->msgs[conn->msg_size];
        msg->path = strdup(filepath);
        if (!msg->path) {
            continue;
        }
        msg->size = (size_t)st.st_size;
        msg->del = 0;
        conn->msg_size++;
    }
    closedir(dir);
    return conn->msg_size;
}

static int auth_userpass(const char * user, const char * password) {
    size_t ulen = strlen(USER);
    size_t plen = strlen(PASS);
    int user_ok = (strlen(user) == ulen) & (gnutls_memcmp(user, USER, ulen) == 0);
    int pass_ok = (strlen(password) == plen) & (gnutls_memcmp(password, PASS, plen) == 0);
    return user_ok & pass_ok;
}

static int parse_msgno(const char *arg) {
    if (!arg || !*arg)
        return -1;
    char *end;
    long v = strtol(arg, &end, 10);
    if (*end != '\0' || v <= 0)
        return -1;
    return (int)v;
}

static int msg_valid(struct session * conn, int n) {
    return n >= 1 && n <= (int)conn->msg_size && !conn->msgs[n - 1].del;
}

static int pop3_cmd_capa(struct session *conn, const char *arg) {
    conn_send(conn, "+OK");
    if (conn->state == STATE_TRANSACTION) {
        conn_send(conn, "LIST");
        conn_send(conn, "TOP");
        conn_send(conn, "RETR");
        conn_send(conn, "UIDL");
        conn_send(conn, "DELE");
        conn_send(conn, "RSET");
    }
    conn_send(conn, "USER");
    conn_send(conn, "RESP-CODES");
    conn_send(conn, "QUIT");
    conn_send(conn, ".");
    return 0;
}

static int req_state(struct session * conn, int req) {
    if (conn->state == req) {
        return 0;
    }
    if (req == STATE_TRANSACTION) {
        conn_send(conn, "-ERR failed");
    } else {
        conn_send(conn, "-ERR authed");
    }
    return -1;
}

static int pop3_cmd_user(struct session * conn, const char * arg) {
    if (req_state(conn, STATE_AUTH) < 0) {
        return 0;
    }
    if (!arg) {
        conn_send(conn, "-ERR");
        return 0;
    }
    strncpy(conn->user_tmp, arg, sizeof(conn->user_tmp) - 1);
    conn->user_tmp[sizeof(conn->user_tmp) - 1] = '\0';
    conn_send(conn, "+OK");
    return 0;
}

static int pop3_cmd_pass(struct session * conn, const char * arg) {
    if (req_state(conn, STATE_AUTH) < 0) {
        return 1;
    }
    if (!conn->user_tmp[0] || !arg || !*arg) {
        LOG("S: bye ");
        return -1;
    }
    if (auth_userpass(conn->user_tmp, arg)) {
        load_mailbox(conn, MAILDIR"/cur");
        conn->state = STATE_TRANSACTION;
        conn_send(conn, "+OK");
        return 0;
    }
    LOG("AUTH FAIL %s", conn->cip);
    conn_send(conn, "-ERR failed bye");
    memset(conn->user_tmp, 0, sizeof(conn->user_tmp));
    return -1;
}

static int pop3_cmd_stat(struct session * conn, const char *arg) {
    if (req_state(conn, STATE_TRANSACTION) < 0) {
        return 0;
    }
    off_t total = 0;
    int count = 0;
    for (int i = 0; i < (int)conn->msg_size; i++) {
        struct mail * m = &conn->msgs[i];
        if (m->del) continue;
        count++;
        total += m->size;
    }
    conn_send(conn, "+OK %d %lld", count, (long long)total);
    return 0;
}

static int pop3_cmd_list(struct session *conn, const char *arg) {
    if (req_state(conn, STATE_TRANSACTION) < 0) {
        return 0;
    }
    if (arg && *arg) {
        int n = parse_msgno(arg);
        if (!msg_valid(conn, n)) {
            LOG("S: no msg %d ", n);
            conn_send(conn, "-ERR");
            return 0;
        }
        conn_send(conn, "+OK %d %lld", n, (long long)conn->msgs[n - 1].size);
        return 0;
    }
    off_t total = 0;
    int count = 0;
    for (int i = 0; i < (int)conn->msg_size; i++) {
        if (!conn->msgs[i].del) {
            count++;
            total += conn->msgs[i].size;
        }
    }
    conn_send(conn, "+OK %d msgs (%lld octets)", count, (long long)total);
    for (int i = 0; i < (int)conn->msg_size; i++) {
        if (conn->msgs[i].del) {
            continue;
        }
        conn_send(conn, "%d %lld", i + 1, (long long)conn->msgs[i].size);
    }
    conn_send(conn, ".");
    return 0;
}

static void msg_uid(const char * fname, char * out) {
    unsigned char digest[16];
    const char *colon = strchr(fname, ':');
    size_t len = colon ? (size_t)(colon - fname) : strlen(fname);

    int ret = gnutls_hash_fast(GNUTLS_DIG_MD5, fname, len, digest);
    if (ret < 0) {
        LOG("msg_uid: %s", gnutls_strerror(ret));
        return;
    }
    for (int k = 0; k < 16; k++) {
        snprintf(out + k * 2, 3, "%02x", digest[k]);
    }
}

static int pop3_cmd_uidl(struct session * conn, const char *arg) {
    if (req_state(conn, STATE_TRANSACTION) < 0){
        return 0;
    }
    char uid[33];
    if (arg && *arg) {
        int n = parse_msgno(arg);
        if (!msg_valid(conn, n)) {
            LOG("S: no msg %d ", n);
            conn_send(conn, "-ERR");
            return 0;
        }
        msg_uid(conn->msgs[n - 1].path, uid);
        conn_send(conn, "+OK %d %s", n, uid);
        return 0;
    }
    conn_send(conn, "+OK");
    for (int i = 0; i < (int)conn->msg_size; i++) {
        struct mail * m = &conn->msgs[i];
        if (m->del) continue;
        msg_uid(m->path, uid);
        conn_send(conn, "%d %s", i + 1, uid);
    }
    conn_send(conn, ".");
    return 0;
}

static size_t mail_truncate(const char *buf, size_t size, int crlf, int max_lines) {
    if (max_lines < 0) return size;
    size_t i = 0;
    while (i < size) {
        if (!crlf && buf[i] == '\n' && i + 1 < size && buf[i + 1] == '\n')
            { i += 2; break; }
        if (crlf  && buf[i] == '\r' && i + 3 < size
                  && buf[i+1] == '\n' && buf[i+2] == '\r' && buf[i+3] == '\n')
            { i += 4; break; }
        i++;
    }
    for (int lines = 0; i < size && lines < max_lines; i++)
        if (buf[i] == '\n') lines++;

    return i;
}

static char *mail_read(const char *path, size_t *out_size) {
    FILE *fp = fopen(path, "rb");
    if (!fp) return NULL;

    char *buf = NULL;
    do {
        if (fseek(fp, 0, SEEK_END) != 0) break;
        long sz = ftell(fp);
        if (sz <= 0 || sz > MAX_MAIL_SIZE) {
            LOG("file error: %s (%ld bytes)", path, sz);
            break;
        }
        rewind(fp);
        buf = malloc((size_t)sz);
        if (!buf) break;
        if (fread(buf, 1, (size_t)sz, fp) != (size_t)sz) {
            free(buf);
            buf = NULL;
            break;
        }
        *out_size = (size_t)sz;
    } while (0);

    fclose(fp);
    return buf;
}

static char *mail_encode(const char *raw, size_t raw_size, int crlf, size_t *out_size) {
    size_t extra = 0;
    for (size_t i = 0; i < raw_size; i++) {
        if (!crlf && raw[i] == '\n' && (i == 0 || raw[i-1] != '\r')) extra++;
        if (raw[i] == '.' && (i == 0 || raw[i-1] == '\n')) extra++;
    }
    char *buf = malloc(raw_size + extra + 5);
    if (!buf) return NULL;
    char *wp = buf;
    for (size_t i = 0; i < raw_size; i++) {
        if (raw[i] == '.' && (i == 0 || raw[i-1] == '\n')) *wp++ = '.';
        if (!crlf && raw[i] == '\n' && (i == 0 || raw[i-1] != '\r')) *wp++ = '\r';
        *wp++ = raw[i];
    }
    if (wp == buf || *(wp - 1) != '\n') { *wp++ = '\r'; *wp++ = '\n'; }
    *wp++ = '.'; *wp++ = '\r'; *wp++ = '\n';
    *out_size = (size_t)(wp - buf);
    return buf;
}

static int mail_send(struct session *conn, int msgno, int max_lines) {
    size_t raw_size = 0;
    char *raw = mail_read(conn->msgs[msgno - 1].path, &raw_size);
    if (!raw) {
        conn_send(conn, "-ERR");
        return 0;
    }
    int crlf = 0;
    for (size_t i = 0; i + 1 < raw_size; i++) {
        if (raw[i] == '\r' && raw[i + 1] == '\n') { crlf = 1; break; }
        if (raw[i] == '\n') { crlf = 0; break; }
    }
    size_t send_size = mail_truncate(raw, raw_size, crlf, max_lines);
    size_t out_size = 0;
    char *out = mail_encode(raw, send_size, crlf, &out_size);
    free(raw);
    if (!out) {
        conn_send(conn, "-ERR");
        return 0;
    }

    if (conn_send(conn, "+OK %zu octets", out_size - 3) < 0) {
        free(out);
        return 0;
    }
    if (sendq_attach(conn, out, out_size) < 0) {
        free(out);
        conn_send(conn, "-ERR");
        return 0;
    }
    return 0;
}

static int parse_retr_args(const char *arg, int *msgno, int *lines) {
    if (!arg || !*arg) return -1;
    char *end;
    long n = strtol(arg, &end, 10);
    if (end == arg || n <= 0) return -1;

    while (*end == ' ' || *end == '\t') end++;
    if (*end == '\0') {
        *msgno = (int)n;
        *lines = -1;
        return 0;
    }

    char *end2;
    long l = strtol(end, &end2, 10);
    if (end2 == end || *end2 != '\0' || l < 0) return -1;
    *msgno = (int)n;
    *lines = (int)l;
    return 0;
}

static int pop3_cmd_retr(struct session *conn, const char *arg) {
    if (req_state(conn, STATE_TRANSACTION) < 0) return 0;
    int n, lines;
    if (parse_retr_args(arg, &n, &lines) < 0 || lines != -1) {
        conn_send(conn, "-ERR invalid");
        return 0;
    }
    if (!msg_valid(conn, n)) {
        conn_send(conn, "-ERR no message");
        return 0;
    }
    return mail_send(conn, n, -1);
}

static int pop3_cmd_top(struct session *conn, const char *arg) {
    if (req_state(conn, STATE_TRANSACTION) < 0) return 0;
    int n, lines;
    if (!arg || parse_retr_args(arg, &n, &lines) < 0 || lines < 0) {
        conn_send(conn, "-ERR invalid");
        return 0;
    }
    if (!msg_valid(conn, n)) {
        conn_send(conn, "-ERR no message");
        return 0;
    }
    return mail_send(conn, n, lines);
}

static int pop3_cmd_noop(struct session *conn, const char *arg) {
    conn_send(conn, "+OK");
    return 0;
}

static int pop3_cmd_dele(struct session *conn, const char *arg) {
    if (req_state(conn, STATE_TRANSACTION) < 0) {
        return 0;
    }
    int n = parse_msgno(arg);
    if (!msg_valid(conn, n)) {
        conn_send(conn, "-ERR no message");
    } else {
        conn->msgs[n - 1].del = 1;
        conn_send(conn, "+OK msg %d del", n);
    }
    return 0;
}

static int pop3_cmd_rset(struct session * conn, const char * arg) {
    if (req_state(conn, STATE_TRANSACTION) < 0) {
        return 0;
    }
    for (int i = 0; i < (int)conn->msg_size; i++) {
        conn->msgs[i].del = 0;
    }
    conn_send(conn, "+OK");
    return 0;
}

static int pop3_cmd_quit(struct session * conn, const char * arg) {
    if(conn->state == STATE_TRANSACTION) {
        for (int i = 0; i < (int)conn->msg_size; i++) {
            struct mail * m = &conn->msgs[i];
            if (!m->del) continue;
            if (unlink(m->path) != 0) {
                LOG("unlink '%s': %s", m->path, strerror(errno));
            }
        }
    }
    conn_send(conn, "+OK bye");
    return 1;
}

typedef int (*cmd_fn)(struct session * conn, const char * arg);

struct pop3_cmd {
    const char *cmd;
    cmd_fn func;
};

static const struct pop3_cmd pop3_cmd_table[] = {
    { "CAPA", pop3_cmd_capa },
    { "USER", pop3_cmd_user },
    { "PASS", pop3_cmd_pass },
    { "STAT", pop3_cmd_stat },
    { "LIST", pop3_cmd_list },
    { "TOP",  pop3_cmd_top },
    { "UIDL", pop3_cmd_uidl },
    { "RETR", pop3_cmd_retr },
    { "NOOP", pop3_cmd_noop },
    { "DELE", pop3_cmd_dele },
    { "RSET", pop3_cmd_rset },
    { "QUIT", pop3_cmd_quit },
};

static int dispatch_pop3_cmd(struct session * conn, const char * cmd, const char * arg) {
    if (!cmd) {
        conn_send(conn, "-ERR");
        return -1;
    }
    size_t cmds = sizeof(pop3_cmd_table) / sizeof(*pop3_cmd_table);
    for (size_t i = 0; i < cmds; i++) {
        const struct pop3_cmd *p = &pop3_cmd_table[i];
        if (!strcmp(p->cmd, cmd))
            return p->func(conn, arg);
    }
    conn_send(conn, "-ERR");
    return -1;
}

static int rbuf_grow(struct session * conn) {
    if (conn->rbuf_cap >= MAX_LINE)
        return -1;
    int new_cap = conn->rbuf_cap * 2;
    if (new_cap > MAX_LINE)
        new_cap = MAX_LINE;
    char *tmp = realloc(conn->rbuf, new_cap);
    if (!tmp) {
        return -1;
    }
    conn->rbuf = tmp;
    conn->rbuf_cap = new_cap;
    return 0;
}

static void rbuf_shrink(struct session * conn) {
    if (conn->rbuf_cap <= RBUF_INIT) return;
    char *tmp = realloc(conn->rbuf, RBUF_INIT);
    if (tmp) {
        conn->rbuf = tmp;
        conn->rbuf_cap = RBUF_INIT;
    }
}

static int process_line(struct session *conn) {
    conn->rbuf[conn->rlen] = '\0';
    conn->rlen = 0;
    LOG("C: %s", conn->rbuf);
    char *saveptr;
    char *cmd = strtok_r(conn->rbuf, " ", &saveptr);
    char *arg = strtok_r(NULL, "", &saveptr);
    int ret = dispatch_pop3_cmd(conn, cmd, arg);
    rbuf_shrink(conn);
    return ret;
}

static int rbuf_append(struct session * conn, char ch) {
    if (conn->rlen + 1 >= conn->rbuf_cap) {
        if (rbuf_grow(conn) < 0)
            return -1;
    }
    conn->rbuf[conn->rlen++] = ch;
    return 0;
}

static void epoll_mod(struct server * srv, struct session * conn, uint32_t events) {
    struct epoll_event ev;
    ev.events = events;
    ev.data.ptr = conn;
    epoll_ctl(srv->epoll_fd, EPOLL_CTL_MOD, conn->fd, &ev);
}

static int process_read(struct server *srv, struct session *conn) {
    char tmp[4096];
    do {
        ssize_t n = gnutls_record_recv(conn->tls, tmp, sizeof(tmp));
        if (n == GNUTLS_E_AGAIN || n == GNUTLS_E_INTERRUPTED) {
            return 0;
        }
        if (n <= 0) {
            return -1;
        }
        conn->expire_at = time(NULL) + SESSION_TIMEOUT_SEC;
        for (ssize_t i = 0; i < n; i++) {
            char ch = tmp[i];
            if (ch == '\n') {
                int r = process_line(conn);
                if (r < 0)
                    return -1;
                if (r > 0)
                    return 1;
            } else if (ch != '\r') {
                if (rbuf_append(conn, ch) < 0)
                    return -1;
            }
        }
    } while (gnutls_record_check_pending(conn->tls) > 0);
    return 0;
}

static int sendq_flush(struct session *conn) {
    while (conn->send_head) {
        struct sendq_node * node = conn->send_head;
        const char * ptr = node->data + node->sent;
        size_t rem = node->size - node->sent;

        ssize_t n = gnutls_record_send(conn->tls, ptr, rem);
        if (n > 0) {
            node->sent += (size_t)n;
            if (node->sent == node->size) {
                conn->send_head = node->next;
                if (!conn->send_head) conn->send_tail = NULL;
                free(node->data);
                free(node);
            }
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
        conn_send(conn, "+OK ready");
        int fr = sendq_flush(conn);
        if (fr < 0) {
            conn_free(srv, conn);
            return;
        }
        epoll_mod(srv, conn, fr > 0 ? EPOLLIN | EPOLLOUT : EPOLLIN);
        return;
    }

    if (gnutls_error_is_fatal(ret)) {
        LOG("handshake fatal %s: %s (errno=%d: %s)", conn->cip, gnutls_strerror(ret), errno, strerror(errno));
        conn_free(srv, conn);
        return;
    }

    int dir = gnutls_record_get_direction(conn->tls);
    epoll_mod(srv, conn, dir ? EPOLLOUT : EPOLLIN);
}

static void handle_conn_io(struct server *srv, struct session *conn, uint32_t events) {
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
    if ((events & EPOLLIN) && conn->phase == CONN_RUNNING) {
        int r = process_read(srv, conn);
        if (r != 0) {
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
    epoll_mod(srv, conn, conn->send_head ? EPOLLIN | EPOLLOUT : EPOLLIN);
}

static void check_timeouts(struct server * srv) {
    time_t now = time(NULL);
    struct session * cur = srv->cons;
    while (cur) {
        struct session * next = cur->next;
        if (now >= cur->expire_at) {
            LOG("TIMEOUT %s %s", cur->cip, cur->phase == CONN_HANDSHAKE ? "handshake" : "session");
            conn_free(srv, cur);
        }
        cur = next;
    }
}

static int create_tls_context(struct server *srv, char *cert, char *key) {
    int ret;
    ret = gnutls_certificate_allocate_credentials(&srv->tls_creds);
    if (ret < 0) {
        return -1;
    }
    ret = gnutls_certificate_set_x509_key_file(srv->tls_creds, cert, key, GNUTLS_X509_FMT_PEM);
    if (ret < 0) {
        fprintf(stderr, "load cert/key failed: %s\n", gnutls_strerror(ret));
        gnutls_certificate_free_credentials(srv->tls_creds);
        return -1;
    }
    ret = gnutls_priority_init(&srv->tls_prio,"NORMAL",NULL);
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
    struct sockaddr_in addr = { .sin_family = AF_INET, .sin_port = htons(port), .sin_addr.s_addr = INADDR_ANY, };
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

static struct session * conn_new(struct server *srv, int cfd, gnutls_session_t tls) {
    struct session * conn = calloc(1, sizeof(struct session));
    if (!conn) {
        return NULL;
    }
    conn->rbuf = malloc(RBUF_INIT);
    if (!conn->rbuf) {
        free(conn);
        return NULL;
    }
    conn->rbuf_cap = RBUF_INIT;
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

static void run_event_loop(struct server *srv) {
    struct epoll_event events[MAX_EVENTS];
    time_t last_check = time(NULL);
    while (g_run) {
        int nfds = epoll_wait(srv->epoll_fd, events, MAX_EVENTS, 1000);
        if (nfds < 0) {
            if (errno != EINTR) {
                perror("epoll_wait");
                break;
            }
            nfds = 0;
        }

        for (int i = 0; i < nfds; i++) {
            struct session *conn = events[i].data.ptr;
            if (!conn) {
                accept_new_connections(srv);
                continue;
            }
            if (conn->phase == CONN_HANDSHAKE) {
                handle_handshake(srv, conn);
            } else {
                handle_conn_io(srv, conn, events[i].events);
            }
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
    close(srv->server_fd);
    close(srv->epoll_fd);
    gnutls_priority_deinit(srv->tls_prio);
    gnutls_certificate_free_credentials(srv->tls_creds);
    gnutls_global_deinit();
}

static void signal_handler(int sig) {
    (void)sig;
    g_run = 0;
}

int main(int argc, char *argv[]) {
    int port = (argc > 1) ? atoi(argv[1]) : PORT;
    char * cert_path = (argc > 2) ? argv[2] : CERT;
    char * key_path = (argc > 3) ? argv[3] : KEY;

    struct server srv = {
        .tls_creds = NULL,
        .tls_prio = NULL,
        .epoll_fd = -1,
        .server_fd = -1,
        .cons = NULL,
    };
    g_run = 1;

    gnutls_global_init();

    signal(SIGPIPE, SIG_IGN);
    signal(SIGINT, signal_handler);
    signal(SIGTERM, signal_handler);

    if (create_tls_context(&srv, cert_path, key_path) < 0) {
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
        close(srv.server_fd);
        cleanup(&srv);
        return EXIT_FAILURE;
    }
    printf("pop3s port=%d\n", port);
    run_event_loop(&srv);
    cleanup(&srv);
    return EXIT_SUCCESS;
}
