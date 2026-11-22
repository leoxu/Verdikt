/* Two real C idioms that need a struct-typed (aggregate) expression used as an rvalue, both from libyaml's
   scanner/parser (DESIGN.md): a chained assignment `a = b = c;` where the type is a plain struct, not a scalar
   (`start_mark = end_mark = token->start_mark;` in yaml's parser.c), and a struct-pointer dereference discarded
   via an explicit `(void)` cast (`(void)POP(stack);`, POP expanding to `*(--stack.top)`). Both used to fail to
   lower: the first because genL's "lvalue of an inner assignment" special case only covered scalar types, the
   second because `(void)x` on a struct lvalue goes through an implicit `CK_LValueToRValue ... part_of_explicit_cast`
   that genR/genCast can't represent for a non-scalar type (genL already knows how to unwrap exactly this cast). */
typedef struct { int index, line, column; } mark_t;

int chained_struct_assign(int v1, int v2, int v3) {
	mark_t a, b, c;
	c.index = v1; c.line = v2; c.column = v3;
	a = b = c;
	return a.index == b.line;
}

typedef struct { mark_t *start, *top, *end; } mark_stack_t;
#define POP(stack) (*(--(stack).top))

int discard_struct_deref(mark_stack_t s, int x) {
	if (x) (void)POP(s);
	return 0;
}
