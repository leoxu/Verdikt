/* The cJSON parse_number idiom: strtod's endptr must point back into the same string object passed as nptr, so
   `endptr - nptr` is a same-object pointer difference, never real UB. Before models/libc.core had a @strtod model,
   this call fell back to the generic opaque-external default, whose output pointer has no guaranteed relation to
   the input object - producing a spurious ptr_cmp_diff_obj on exactly this real-world idiom (DESIGN.md has the
   full writeup, found scanning cJSON). */
#include <stdlib.h>

long parse_leading_number(const char *s) {
	char *end = NULL;
	double v = strtod(s, &end);
	(void)v;
	return (long)(end - s);
}
