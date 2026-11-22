// `container_of(ptr, T, member)` -- `(T *)((char *)ptr - offsetof(T, member))` -- and the one place it is
// routinely, deliberately out of bounds (DESIGN.md §22.368).
//
// `list_for_each_entry` starts with `pos = container_of(head->next, T, member)`. On an EMPTY list
// `head->next == head`, so that computes a pointer BEFORE whatever object the list head lives in; the very next
// thing it does is test `&pos->member != head`, which is false, so the body never runs and the pointer is never
// dereferenced. Strictly UB in C, universal in practice.
//
// This stayed invisible until the project initialiser started being executed: it is initialisation that registers
// these lists, and only then do the handlers walk them. In sound/core round 49b every single one of the 87
// "confirmed" findings was this, at `snd_info_register`; in round 49f it was still four entry-visible sites
// (`snd_pcm_get`, `snd_pcm_next`, `snd_hwdep_search`, `snd_rawmidi_search`) plus most of 257 warnings.
//
// Only the pointer ARITHMETIC check is waived, and only on this exact shape. A container_of result that really is
// dereferenced out of bounds is still a finding -- `demo_co_deref` below is here to keep that true, because a
// waiver that also swallowed the dereference would turn a whole class of real defects silent.

struct list_head {
  struct list_head *next, *prev;
};

struct item {
  int before;            // makes offsetof(struct item, link) non-zero, so the subtraction really moves
  struct list_head link;
  int value;
};

#define offsetof_link ((unsigned long)&((struct item *)0)->link)

// TWO spellings, and both must be covered. The first version of this waiver only accepted the `(char *)` form,
// which is what this fixture used -- so the fixture passed while sound/core was completely unaffected, and the
// change looked done. The kernel's macro goes through a `void *` local instead, and Clang reports `void` as width
// ZERO (not 1), so a "pointee is one byte" test silently rejects every real container_of. A fixture that does not
// spell the construct the way the target spells it proves nothing.
#define item_of(p) ((struct item *)((char *)(p) - offsetof_link))
#define item_of_k(p) ({ void *__mptr = (void *)(p); ((struct item *)(__mptr - offsetof_link)); })

static struct list_head the_list = {&the_list, &the_list};   // an EMPTY list: next == prev == itself

// The idiom, on an empty list: `it` is computed before `the_list`'s object and then only compared. No finding.
int demo_co_empty_walk(unsigned n) {
  struct list_head *p;
  int sum = 0;
  (void)n;
  for (p = the_list.next; p != &the_list; p = p->next) sum += item_of(p)->value;
  return sum;
}

// The same arithmetic with no loop guard at all: still only arithmetic, still no dereference, still no finding.
int demo_co_arith_only(unsigned n) {
  struct item *it = item_of(&the_list);
  (void)n;
  return it != 0;
}

// The kernel's own spelling of the same thing: `void *__mptr` inside a statement expression. This is the one that
// matters in practice, and the one the first version of the waiver missed.
int demo_co_kernel_walk(unsigned n) {
  struct list_head *p;
  int sum = 0;
  (void)n;
  for (p = the_list.next; p != &the_list; p = p->next) sum += item_of_k(p)->value;
  return sum;
}

// ... and the control that keeps the waiver honest: the result IS dereferenced, out of bounds. `the_list` is a
// 16-byte object and `item_of` points 4 bytes before it, so reading `->value` (at offset 20 of a struct item,
// i.e. 16 bytes past the list head's start) is a real out-of-bounds read, and it must still be reported.
int demo_co_deref(unsigned n) {
  struct item *it = item_of(&the_list);
  (void)n;
  return it->value;
}
