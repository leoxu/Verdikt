/* `dlsym(handle, "literal")` resolved to the function the scan linked (DESIGN.md §22.424).
 *
 * Without the resolution, `dlsym` hands back an address no call site can match, the call through it is
 * `__hlir_unknown_indirect`, and everything the shared object provides is invisible -- which is the whole
 * point of the dlopen path. Here the plugin's defect is three frames down from the entry, behind two NULL
 * checks, so it is only reachable if the name actually resolves.
 *
 * `dlsym_computed` is the control: the same call with a name the frontend cannot read. It must NOT resolve --
 * inventing a target for it would be a guess, not an analysis.
 */
#include <dlfcn.h>

typedef int (*parse_fn)(const unsigned char *, unsigned);

int dlsym_literal(const unsigned char *in, unsigned caplen)
{
	void *h;
	parse_fn fn;

	h = dlopen("libplugin.so", 2);
	if (!h)
		return -1;
	fn = (parse_fn)dlsym(h, "plugin_parse");
	if (!fn)
		return -2;
	return fn(in, caplen);
}

int dlsym_computed(const unsigned char *in, unsigned caplen)
{
	void *h;
	parse_fn fn;
	char nm[13];

	__builtin_memcpy(nm, "plugin_parse", 13);
	h = dlopen("libplugin.so", 2);
	if (!h)
		return -1;
	fn = (parse_fn)dlsym(h, nm);
	if (!fn)
		return -2;
	return fn(in, caplen);
}
