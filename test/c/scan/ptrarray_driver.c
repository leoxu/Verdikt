#include <stddef.h>
typedef struct obj { int type; void *ptr; } obj;
typedef struct client { int id; int argc; obj **argv; } client;
int get_cmd(client *c) {
	obj *k = c->argv[1];
	if (c->argc > 2) return ((char *)c->argv[2]->ptr)[0];
	return k->type;
}
int bad_cmd(client *c) { return c->argv[c->argc]->type; }
