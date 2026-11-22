/* DESIGN.md Sec.22.457. A memcpy whose length is TAINTED is concretised by the concolic domain to this
 * run's value; writing the destination unguarded would drop the bytes' dependence on that length while
 * the destination object's SIZE keeps it, and the solver can then answer a bounds query by picking a
 * length the copy contradicts. The first function is the shape that produced such a witness; the other
 * two are the real defects the guard must not hide. */
#include <stdlib.h>
#include <string.h>

/* The NUL-termination contract every C-string harness in scan-profiles/ is built on: exactly in_len
 * attacker bytes plus one terminator. strlen() cannot run off the end -- no finding. */
int
symlen_terminated(const unsigned char *in, unsigned int in_len)
{
	char	   *buf;
	size_t		n;

	if (in_len == 0 || in_len > 48)
		return -1;
	buf = malloc((size_t) in_len + 1);
	if (!buf)
		return -2;
	memcpy(buf, in, in_len);
	buf[in_len] = '\0';
	n = strlen(buf);
	free(buf);
	return (int) n;
}

/* REAL oob_write: four bytes of destination, up to 48 of attacker length. */
int
symlen_memcpy_ovf(const unsigned char *in, unsigned int in_len)
{
	char	   *dst;
	int			r;

	if (in_len == 0 || in_len > 48)
		return -1;
	dst = malloc(4);
	if (!dst)
		return -2;
	memcpy(dst, in, in_len);
	r = dst[0];
	free(dst);
	return r;
}

/* REAL oob_read: no room for a terminator and none written, so strlen runs past the end. */
int
symlen_strlen_ovf(const unsigned char *in, unsigned int in_len)
{
	char	   *buf;
	size_t		n;

	if (in_len == 0 || in_len > 48)
		return -1;
	buf = malloc((size_t) in_len);
	if (!buf)
		return -2;
	memcpy(buf, in, in_len);
	n = strlen(buf);
	free(buf);
	return (int) n;
}

/* The overflow needs a length the seed does not take. Pinning the concretised length must not stop the
 * engine SOLVING for one: memcpy's own bounds check runs before the pin, so this is still reachable. */
int
symlen_solve_ovf(const unsigned char *in, unsigned int in_len)
{
	char	   *dst;
	int			r;

	if (in_len == 0 || in_len > 48)
		return -1;
	dst = malloc(4);
	if (!dst)
		return -2;
	memcpy(dst, in, in_len);
	r = dst[0];
	free(dst);
	return r;
}
