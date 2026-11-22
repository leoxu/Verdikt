#include <stdint.h>
#include <stddef.h>
struct wl_client; struct wl_resource;
void *wl_resource_get_user_data(struct wl_resource *r);
void wl_resource_set_user_data(struct wl_resource *r, void *d);
void wl_resource_post_error(struct wl_resource *r, uint32_t code, const char *fmt, ...);
struct planes { int n; int fd[4]; uint32_t offset[4]; void *aux; };
struct planes_aux { char name[8]; };

static void add_plane(struct wl_client *client, struct wl_resource *res, int fd, uint32_t idx, uint32_t offset)
{
	struct planes *p = wl_resource_get_user_data(res);
	if (!p) return;
	if (idx >= 4) { wl_resource_post_error(res, 1, "idx"); return; }
	if (p->fd[idx] != -1) { wl_resource_post_error(res, 2, "set"); return; }
	p->fd[idx] = fd;
	p->offset[idx] = offset;
	p->n++;
}
static void bug_plane(struct wl_client *client, struct wl_resource *res, uint32_t idx)
{
	struct planes *p = wl_resource_get_user_data(res);
	p->fd[idx] = 0;   /* no bound check: idx is attacker controlled */
}
struct iface { void (*add)(struct wl_client *, struct wl_resource *, int, uint32_t, uint32_t); void (*bug)(struct wl_client *, struct wl_resource *, uint32_t); };
const struct iface table = { add_plane, bug_plane };

/* the handle is only passed down: the user data type propagates to the caller's parameter */
static void add_common(struct wl_client *client, struct wl_resource *res, uint32_t idx)
{
	struct planes *p = wl_resource_get_user_data(res);
	if (idx < 4) p->fd[idx] = -1;
}
static void add_outer(struct wl_client *client, struct wl_resource *res, uint32_t idx)
{
	add_common(client, res, idx);
}
const struct iface table2 = { 0, 0 };
void (*outer_cb)(struct wl_client *, struct wl_resource *, uint32_t) = add_outer;

/* the callee frees its user data: the object must be a heap object (no invalid_free) */
void free(void *p);
static void free_plane(struct wl_client *client, struct wl_resource *res, uint32_t unused)
{
	struct planes *p = wl_resource_get_user_data(res);
	free(p);
}
void (*free_cb)(struct wl_client *, struct wl_resource *, uint32_t) = free_plane;
