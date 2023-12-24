/*
 *  cghttpd by Davide Libenzi (coronet/guasi based HTTP server)
 *  Copyright (C) 2007  Davide Libenzi
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 *  Davide Libenzi <davidel@xmailserver.org>
 *
 */

#define _GNU_SOURCE
#include <sys/types.h>
#include <sys/time.h>
#include <sys/ioctl.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <stdarg.h>
#include <limits.h>
#include <signal.h>
#include <dirent.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <arpa/nameser.h>
#include <netdb.h>

/*
 * You need the Portable Coroutine Library (PCL) to build this source.
 * You can find a copy of PCL source code at :
 *
 *             http://www.xmailserver.org/libpcl.html
 *
 * Or, many distributions has a package for it (Debian names it "libpcl1-dev").
 * To install:
 *
 * $ ./configure --prefix=/usr
 * $ make
 * # make install
 *
 */
#include <pcl.h>

/*
 * You need the Coronet library to build this source.
 * You can find a copy of the Coronet library source code at :
 *
 *             http://www.xmailserver.org/coronet-lib.html
 *
 * $ ./configure --prefix=/usr
 * $ make
 * # make install
 *
 */
#include <coronet.h>

/*
 * You need the GUASI library to build this source.
 * You can find a copy of the GUASI library source code at :
 *
 *             http://www.xmailserver.org/guasi-lib.html
 *
 * $ ./configure --prefix=/usr
 * $ make
 * # make install
 */
#include <guasi.h>
#include <guasi_syscalls.h>




#define CGHTTPD_MIN_THREADS 32
#define CGHTTPD_MAX_THREADS 256
#define CGHTTPD_MAX_PRIORITY 1
#define CGHTTPD_STKSIZE (1024 * 8)
#define CGHTTPD_LISTEN_SIZE 1024
#define CGHTTPD_CONET_COOKIE ((void *) 1)
#define CGHTTPD_TIMEO 2000
#define CGHTTPD_MAX_REQS 256

/*
 * Submits a syscall and resume to the calling coroutine, until
 * the syscall completion will reschedule us.
 */
#define CGHTTPD_SYSCALL(res, name, ...) do { \
	struct cghttpd_async_ctx ctx; \
	ctx.co = co_current(); \
	ctx.result = 0; \
	ctx.done = 0; \
	do { \
		guasi__ ##name(hctx, NULL, &ctx, 0, __VA_ARGS__); \
		co_resume(); \
	} while (!ctx.done); \
	res = (__typeof(res)) ctx.result; \
} while (0);



struct cghttpd_async_ctx {
	coroutine_t co;
	guasi_param_t result;
	int done;
};




static int cghttpd_set_cork(int fd, int v);
static int cghttpd_send_mem(struct sk_conn *conn, long size, char const *ver,
			    char const *cclose);
static int cghttpd_send_doc(struct sk_conn *conn, char const *doc, char const *ver,
			    char const *cclose);
static int cghttpd_send_url(struct sk_conn *conn, char const *doc, char const *ver,
			    char const *cclose);
static void *cghttpd_service(void *data);
static void *cghttpd_acceptor(void *data);
static guasi_param_t cghttpd__conet_events_wait(void *priv, guasi_param_t const *params);
static guasi_req_t cghttpd_scheule_epw(int epwtimeo);
static void cghttpd_epoll_dispatch(int nfds);
static void cghttpd_scheduler(void);
static void cghttpd_sigint(int sig);
static void cghttpd_usage(char const *prg);




static int stopsvr;
static char const *rootfs = ".";
static int svr_port = 80;
static int oflags;
static guasi_t hctx;
static int lsnbklog = CGHTTPD_LISTEN_SIZE;
static int min_threads = CGHTTPD_MIN_THREADS, max_threads = CGHTTPD_MAX_THREADS;
static int stksize = CGHTTPD_STKSIZE;
static unsigned long long conns, reqs, tbytes;




static int cghttpd_set_cork(int fd, int v) {

	return setsockopt(fd, SOL_TCP, TCP_CORK, &v, sizeof(v));
}

static int cghttpd_send_mem(struct sk_conn *conn, long size, char const *ver,
			    char const *cclose) {
	size_t csize, n;
	long msent;
	static char mbuf[1024 * 8];

	cghttpd_set_cork(conn->sfd, 1);
	conet_printf(conn,
		     "%s 200 OK\r\n"
		     "Connection: %s\r\n"
		     "Content-Length: %ld\r\n"
		     "\r\n", ver, cclose, size);
	for (msent = 0; msent < size;) {
		csize = (size - msent) > sizeof(mbuf) ?
			sizeof(mbuf): (size_t) (size - msent);
		if ((n = conet_write(conn, mbuf, csize)) > 0)
			msent += n;
		if (n != csize)
			break;
	}
	cghttpd_set_cork(conn->sfd, 0);

	tbytes += msent;

	return msent == size ? 0: -1;
}

static int cghttpd_send_doc(struct sk_conn *conn, char const *doc, char const *ver,
			    char const *cclose) {
	int fd, error;
	goff_t off;
	char *path;
	struct stat stbuf;

	/*
	 * Ok, this is a dumb server, don't expect protection against '..'
	 * root path back-tracking tricks ;)
	 */
	asprintf(&path, "%s/%s", rootfs, *doc == '/' ? doc + 1: doc);
	if (path == NULL) {
		perror("malloc");
		conet_printf(conn,
			     "%s 500 Internal server error\r\n"
			     "Connection: %s\r\n"
			     "Content-Length: 0\r\n"
			     "\r\n", ver, cclose);
		return -1;
	}
	CGHTTPD_SYSCALL(fd, open, path, oflags | O_RDONLY, 0);
	if (fd == -1) {
		perror(path);
		free(path);
		conet_printf(conn,
			     "%s 404 Not found\r\n"
			     "Connection: %s\r\n"
			     "Content-Length: 0\r\n"
			     "\r\n", ver, cclose);
		return -1;
	}
	free(path);
	CGHTTPD_SYSCALL(error, fstat, fd, &stbuf);
	cghttpd_set_cork(conn->sfd, 1);
	conet_printf(conn,
		     "%s 200 OK\r\n"
		     "Connection: %s\r\n"
		     "Content-Length: %lld\r\n"
		     "\r\n", ver, cclose, (long long) stbuf.st_size);
	for (off = 0; off < stbuf.st_size;) {
		CGHTTPD_SYSCALL(error, sendfile, conn->sfd, fd, &off,
				(size_t) (stbuf.st_size - off));
		if (error == -1 && errno != EAGAIN && errno != EWOULDBLOCK) {
			perror("sendfile");
			break;
		}
	}
	close(fd);
	cghttpd_set_cork(conn->sfd, 0);

	tbytes += off;

	return off == stbuf.st_size ? 0: -1;
}

static int cghttpd_send_url(struct sk_conn *conn, char const *doc, char const *ver,
			    char const *cclose) {
	int error;

	if (strncmp(doc, "/mem-", 5) == 0)
		error = cghttpd_send_mem(conn, atol(doc + 5), ver, cclose);
	else
		error = cghttpd_send_doc(conn, doc, ver, cclose);

	return error;
}

static void *cghttpd_service(void *data) {
	int cfd = (int) (long) data;
	int cclose = 0, chunked, lsize, clen;
	char *req, *meth, *doc, *ver, *ln, *auxptr;
	struct sk_conn *conn;

	if ((conn = conet_new_conn(cfd, co_current())) == NULL)
		return NULL;
	while (!stopsvr && !cclose) {
		if ((req = conet_readln(conn, &lsize)) == NULL)
			break;
		if ((meth = strtok_r(req, " ", &auxptr)) == NULL ||
		    (doc = strtok_r(NULL, " ", &auxptr)) == NULL ||
		    (ver = strtok_r(NULL, " \r\n", &auxptr)) == NULL ||
		    strcasecmp(meth, "GET") != 0) {
			bad_request:
			free(req);
			conet_printf(conn,
				     "HTTP/1.1 400 Bad request\r\n"
				     "Connection: close\r\n"
				     "Content-Length: 0\r\n"
				     "\r\n");
			break;
		}
		reqs++;
		cclose = strcasecmp(ver, "HTTP/1.1") != 0;
		for (clen = 0, chunked = 0;;) {
			if ((ln = conet_readln(conn, &lsize)) == NULL)
				break;
			if (strcmp(ln, "\r\n") == 0) {
				free(ln);
				break;
			}
			if (strncasecmp(ln, "Content-Length:", 15) == 0) {
				for (auxptr = ln + 15; *auxptr == ' '; auxptr++);
				clen = atoi(auxptr);
			} else if (strncasecmp(ln, "Connection:", 11) == 0) {
				for (auxptr = ln + 11; *auxptr == ' '; auxptr++);
				cclose = strncasecmp(auxptr, "close", 5) == 0;
			} else if (strncasecmp(ln, "Transfer-Encoding:", 18) == 0) {
				for (auxptr = ln + 18; *auxptr == ' '; auxptr++);
				chunked = strncasecmp(auxptr, "chunked", 7) == 0;
			}
			free(ln);
		}
		/*
		 * Sorry, really stupid HTTP server here. Neither GET payload nor
		 * chunked encoding allowed.
		 */
		if (clen || chunked)
			goto bad_request;
		cghttpd_send_url(conn, doc, ver, cclose ? "close": "keep-alive");
		free(req);
	}
	conet_close_conn(conn);

	return data;
}

static void *cghttpd_acceptor(void *data) {
	int sfd = (int) (long) data;
	int cfd, addrlen = sizeof(struct sockaddr_in);
	coroutine_t co;
	struct sk_conn *conn;
	struct sockaddr_in addr;

	if ((conn = conet_new_conn(sfd, co_current())) == NULL)
		return NULL;
	while (!stopsvr &&
	       (cfd = conet_accept(conn, (struct sockaddr *) &addr,
				   &addrlen)) != -1) {
		conns++;
		if ((co = co_create((void *) cghttpd_service, (void *) (long) cfd, NULL,
				    stksize)) == NULL) {
			fprintf(stderr, "Unable to create coroutine\n");
			close(cfd);
		} else
			co_call(co);
	}
	conet_close_conn(conn);

	return data;
}

static guasi_param_t cghttpd__conet_events_wait(void *priv, guasi_param_t const *params) {

	return conet_events_wait((int) params[0]);
}

static guasi_req_t cghttpd_scheule_epw(int epwtimeo) {

	return guasi_submit(hctx, NULL, CGHTTPD_CONET_COOKIE, 0,
			    cghttpd__conet_events_wait, NULL, 1, (guasi_param_t) epwtimeo);
}

static void cghttpd_epoll_dispatch(int nfds) {

	conet_events_dispatch(0);
	cghttpd_scheule_epw(-1);
}

static void cghttpd_scheduler(void) {
	int i, nreqs;
	struct cghttpd_async_ctx *ctx;
	struct guasi_reqinfo rinf;
	guasi_req_t reqs[CGHTTPD_MAX_REQS];

	if ((nreqs = guasi_fetch(hctx, reqs, 1, CGHTTPD_MAX_REQS,
				 CGHTTPD_TIMEO)) > 0) {
		for (i = 0; i < nreqs; i++) {
			guasi_req_info(reqs[i], &rinf);
			guasi_req_free(reqs[i]);
			if (rinf.asid == CGHTTPD_CONET_COOKIE)
				cghttpd_epoll_dispatch(rinf.result);
			else {
				ctx = (struct cghttpd_async_ctx *) rinf.asid;

				/*
				 * Sets "errno" so that the caller will find the
				 * proper error code in a POSIX friendly way.
				 */
				errno = rinf.error;
				ctx->result = rinf.result;
				ctx->done++;
				co_call(ctx->co);
			}
		}
	}
}

static void cghttpd_sigint(int sig) {

	stopsvr++;
}

static void cghttpd_usage(char const *prg) {

	fprintf(stderr, "Use: %s [-p PORT (%d)] [-r ROOTFS ('%s')] [-L LSNBKLOG (%d)]\n"
		"\t[-S STKSIZE (%d)] [-m MINTHREAD (%d)] [-M MAXTHREADS (%d)] [-N] [-h]\n",
		prg, svr_port, rootfs, lsnbklog, stksize, CGHTTPD_MIN_THREADS,
		CGHTTPD_MAX_THREADS);
}

int main(int ac, char **av) {
	int i, sfd, one = 1;
	coroutine_t co;
	struct linger ling = { 0, 0 };
	struct sockaddr_in addr;

	for (i = 1; i < ac; i++) {
		if (strcmp(av[i], "-m") == 0) {
			if (++i < ac)
				min_threads = atoi(av[i]);
		} else if (strcmp(av[i], "-M") == 0) {
			if (++i < ac)
				max_threads = atoi(av[i]);
		} else if (strcmp(av[i], "-r") == 0) {
			if (++i < ac)
				rootfs = av[i];
		} else if (strcmp(av[i], "-S") == 0) {
			if (++i < ac)
				stksize = atoi(av[i]);
		} else if (strcmp(av[i], "-p") == 0) {
			if (++i < ac)
				svr_port = atoi(av[i]);
		} else if (strcmp(av[i], "-L") == 0) {
			if (++i < ac)
				lsnbklog = atoi(av[i]);
		} else if (strcmp(av[i], "-N") == 0) {
			oflags |= O_NOATIME;
		} else {
			break;
		}
	}
	signal(SIGINT, cghttpd_sigint);
	signal(SIGPIPE, SIG_IGN);
	siginterrupt(SIGINT, 1);
	if ((hctx = guasi_create(min_threads, max_threads, CGHTTPD_MAX_PRIORITY)) == NULL) {
		fprintf(stderr, "Unable to initialize the GUASI library\n");
		return 1;
	}
	if (conet_init() < 0) {
		fprintf(stderr, "Unable to initialize the Coronet library\n");
		guasi_free(hctx);
		return 2;
	}
	if ((sfd = conet_socket(AF_INET, SOCK_STREAM, 0)) == -1) {
		conet_cleanup();
		guasi_free(hctx);
		return 3;
	}
	setsockopt(sfd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
	setsockopt(sfd, SOL_SOCKET, SO_LINGER, &ling, sizeof(ling));

	addr.sin_family = AF_INET;
	addr.sin_port = htons(svr_port);
	addr.sin_addr.s_addr = htonl(INADDR_ANY);
	if (bind(sfd, (struct sockaddr *) &addr, sizeof(addr)) == -1) {
		perror("bind");
		close(sfd);
		conet_cleanup();
		guasi_free(hctx);
		return 4;
	}
	listen(sfd, lsnbklog);
	if ((co = co_create((void *) cghttpd_acceptor, (void *) (long) sfd, NULL,
			    stksize)) == NULL) {
		fprintf(stderr, "Unable to create coroutine\n");
		close(sfd);
		conet_cleanup();
		guasi_free(hctx);
		return 5;
	}
	co_call(co);
	cghttpd_scheule_epw(-1);

	while (!stopsvr) {
		cghttpd_scheduler();
	}

	conet_cleanup();
	guasi_free(hctx);

	fprintf(stdout,
		"Connections .....: %llu\n"
		"Requests ........: %llu\n"
		"Total Bytes .....: %llu\n", conns, reqs, tbytes);

	return 0;
}

