/*
 * Attacker data (a packet) passes through many layers before it reaches a memcpy:
 *   handle_packet_* -> parse_header -> dispatch -> handle_data -> process_record -> decode_field -> copy_field -> append_to_buf -> memcpy
 * The length is read from the packet, adjusted at several layers, stored in a struct and read back, and only one policy field
 * decides whether the destination bound is enforced: handle_packet_bad configures a limit that is too large, handle_packet_ok the
 * right one. A second chain validates an 8-bit truncation of a 16-bit length in one layer and uses the full length in another.
 */
#include <stddef.h>
#include <string.h>

struct ctx {
	unsigned char buf[32];
	unsigned used;
	unsigned limit;      /* the policy: largest field accepted */
	unsigned pending;    /* a length parked in the struct between layers */
};

static int append_to_buf(struct ctx *c, const unsigned char *src, unsigned n) {
	memcpy(c->buf + c->used, src, n);              /* the sink: buf has 32 bytes */
	c->used += n;
	return 0;
}
static int copy_field(struct ctx *c, const unsigned char *src, unsigned flen) { return append_to_buf(c, src, flen); }
static int decode_field(struct ctx *c, const unsigned char *rec, unsigned off, unsigned flen) { return copy_field(c, rec + off, flen); }

static int process_record(struct ctx *c, const unsigned char *rec, unsigned reclen) {
	if (reclen < 2) return -1;
	unsigned off = 2, flen = rec[1];
	if (off + flen > reclen) return -1;            /* the source bound is checked ... */
	c->pending = flen;                             /* ... the field length is parked in the struct */
	if (c->pending > c->limit) return -1;          /* ... and the destination policy is applied to the parked value */
	return decode_field(c, rec, off, c->pending);
}
static int handle_data(struct ctx *c, const unsigned char *body, unsigned blen) { return process_record(c, body, blen); }
static int dispatch(struct ctx *c, unsigned type, const unsigned char *body, unsigned blen) {
	switch (type) {
	case 1: return handle_data(c, body, blen);
	case 2: return 0;
	default: return -1;
	}
}
static int parse_header(struct ctx *c, const unsigned char *raw, size_t rawlen) {
	if (rawlen < 4) return -1;
	unsigned type = raw[0];
	unsigned blen = ((unsigned)raw[1] << 8) | raw[2];
	if (blen > rawlen - 3) return -1;
	return dispatch(c, type, raw + 3, blen);
}

int handle_packet_bad(const unsigned char *raw, size_t rawlen) {
	struct ctx c = { {0}, 0, 255, 0 };             /* limit 255 > sizeof buf */
	return parse_header(&c, raw, rawlen);
}
int handle_packet_ok(const unsigned char *raw, size_t rawlen) {
	struct ctx c = { {0}, 0, 32, 0 };              /* limit == sizeof buf, used == 0 */
	return parse_header(&c, raw, rawlen);
}

/* ---- chain 2: validation on a truncated copy, use of the full value */
struct msg { unsigned short len; unsigned char body[300]; };
static int check_len(unsigned char n) { return n <= 31; }                    /* 8-bit: 256 + 5 passes as 5 */
static int store_msg(unsigned char *dst, const unsigned char *src, unsigned short len) { memcpy(dst, src, len); return len; }
static int accept_msg(unsigned char *dst, const struct msg *m) {
	if (!check_len(m->len)) return -1;             /* implicit truncation of the 16-bit length */
	return store_msg(dst, m->body, m->len);        /* the full 16-bit length is used */
}
static int route_msg(unsigned char *dst, const struct msg *m) { return accept_msg(dst, m); }
int handle_msg_trunc(const struct msg *m) {
	unsigned char slot[32];
	return route_msg(slot, m);
}
static int check_len_ok(unsigned short n) { return n <= 31; }
static int accept_msg_ok(unsigned char *dst, const struct msg *m) {
	if (!check_len_ok(m->len)) return -1;
	return store_msg(dst, m->body, m->len);
}
int handle_msg_ok(const struct msg *m) {
	unsigned char slot[32];
	return accept_msg_ok(slot, m);
}
