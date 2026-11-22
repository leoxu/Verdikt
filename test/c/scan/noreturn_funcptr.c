/* `noreturn` stated on a function-pointer TYPE, not on a function declaration.
 *
 * __attribute__((noreturn)) is part of the function type, so it survives on a pointer -- and that is the only
 * place a program can state the fact when the call goes through a struct field. tcpdump's netdissect.h does
 * exactly this:
 *
 *     void NORETURN_FUNCPTR (*ndo_error)(netdissect_options *, const char *, ...);
 *
 * Read only off FunctionDecl::isNoReturn() the guarded dereference below looks like a null deref, which is a
 * false positive on a program that declared the fact itself. `die_plain` is the control: same shape, same
 * guard, no attribute on the type -- there the engine must still report the deref, or the fix would be
 * suppressing real bugs rather than honouring a declaration. */
#include <stdlib.h>

struct ops_nr {
	void __attribute__((noreturn)) (*fail)(const char *);
};
struct ops_plain {
	void (*fail)(const char *);
};

extern void bail(const char *);        /* opaque: only the TYPE says anything */
extern void maybe_bail(const char *);

int die_noreturn(unsigned n) {
	char b[8];
	struct ops_nr o;
	o.fail = (void __attribute__((noreturn)) (*)(const char *))bail;
	if (n >= sizeof b) (*o.fail)("out of range");
	b[n] = 1;                /* unreachable with n >= 8: the type says fail() does not return */
	return b[n];
}

int die_plain(unsigned n) {
	char b[8];
	struct ops_plain o;
	o.fail = maybe_bail;
	if (n >= sizeof b) (*o.fail)("out of range");
	b[n] = 1;                /* REACHABLE with n >= 8: nothing says fail() cannot return */
	return b[n];
}
