// libdl models (DESIGN.md §22.423).
//
// The defect below sits behind the dlopen/dlsym gate, so the fixture pins that the gate stays PASSABLE.
//
// It does not prove the models are what makes it passable, and it was written believing it would: an opaque
// external's pointer result is "NULL or a zeroed object", a nondet, so the success branch was reachable
// before the models existed too. What the models change here is `opaque_calls` (3 -> 0) and coverage
// (11 -> 14 blocks). The measurement is in `models/libc.core` above the libdl section.
#include <stdlib.h>

void *dlopen(const char *file, int mode);
void *dlsym(void *handle, const char *name);
int dlclose(void *handle);

static unsigned char g_tab[8];

int dl_entry(const unsigned char *in, unsigned caplen)
{
	void *h;
	void *fn;
	unsigned idx;

	if (caplen < 4)
		return -1;

	h = dlopen("libplugin.so", 2);
	if (h == 0)
		return -2;              /* load failed: nothing below is reachable */

	fn = dlsym(h, "plugin_init");
	if (fn == 0) {
		dlclose(h);
		return -3;
	}

	idx = in[0];
	g_tab[idx & 0x0f] = in[1];      /* reachable only past the dlopen gate; 0x0f overruns g_tab[8] */
	dlclose(h);
	return (int)g_tab[0];
}
