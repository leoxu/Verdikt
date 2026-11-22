// A length tied to its buffer by an equality relation (`bytes == size(ib)`) must stay free to take any legal value:
// the object size used to be an untainted nondet fixed to its seed (64), which pinned `bytes` to 64 too, so the
// branch below was never flipped and the entry came out safe (ntfs3 check_index_buffer, DESIGN.md §22.348).
#include <stdint.h>

struct indx { uint32_t sign; uint16_t fix_off, fix_num; uint64_t lsn, vbn; uint32_t de_off, used, total, flags; };

int check_indx(const struct indx *ib, uint32_t bytes)
{
	if (ib->sign != 0x58444e49)
		return 0;
	if ((ib->fix_num - 1) * 512 != bytes)  /* bytes must be a whole number of sectors: never 64 */
		return 0;
	return ((const uint8_t *)ib)[ib->used];  /* used is not checked against bytes */
}
