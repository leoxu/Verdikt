// The SYMBOLIC engine's replay path, end to end (DESIGN.md §22.419).
//
// Pipeline.cpp has two replays: Taint.cpp's (concolic) and its own (symbolic). The second one used to run with a
// DEFAULT RunConfig -- `models == nullptr` -- so the first call to a function with no body ended it as
// `Unsupported`, and any symbolic finding whose path touched one ModelDB model could never be confirmed. Nothing
// in the suite noticed: there was not one assertion anywhere about `engine == "symbolic"`. tcpdump CVE-2017-12988
// was lost to it, and only became visible because the finding sat on the exact line of a known CVE's patch.
//
// The fixture needs all three of these at once, and the first version of it had only the first two:
//   * a tainted POINTER value, so the concolic pass reports `concretized > 0` and the driver escalates to the
//     symbolic engine at all;
//   * a defect the symbolic engine is the one to find;
//   * a call to a function whose semantics come from the ModelDB (`models/libc.yaml`) rather than from a body
//     linked out of `models/libc.core`. `memcpy`/`strtol` are the WRONG choice: their bodies are linked in, so
//     the replay never needs a ModelProvider and the regression stays invisible. `printf` is a ModelDB model --
//     and it is also what tcpdump's `ND_PRINT` lowers to, which is why the CVE hit this and the first fixture
//     did not.
#include <stdio.h>
#include <string.h>

int sym_replay(const unsigned char *in, unsigned in_len)
{
	unsigned char buf[32];
	const unsigned char *p, *end;
	int sum = 0;

	if (in_len < 32)
		return -1;
	memcpy(buf, in, 32);

	printf("%u\n", (unsigned)buf[1]);   /* ModelDB model, ON THE PATH to the defect below */

	end = buf + 32;
	p = buf + (buf[0] & 0x0f);          /* attacker-controlled POINTER: followed concretely by the concolic pass */

	while (p < end) {
		if (*p == 0xAA)
			break;
		p += (unsigned)(*p & 0x07) + 1;
	}
	sum += *p;                          /* p can be past `end`: the loop steps over it */
	return sum;
}
