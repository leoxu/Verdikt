// CVE:    CVE-2023-53154
// SOURCE: cJSON cJSON.c:787 (parse_string) reached from parse_object:1666, fix adds
//         `if (cannot_access_at_index(input_buffer, 1)) goto fail;`
// KIND:   oob_read
// VULN:   parse_object_vuln
// FIXED:  parse_object_fixed
//
// `parse_object` consumes a `,` and advances, then calls `parse_string`, which dereferences
// `buffer_at_offset(input_buffer)[0]` with `offset == length` -- one byte past the caller's buffer. The
// document `{"a":1,` is enough.
//
// The buffer must be EXACTLY the document's length, with no NUL terminator, or the over-read lands inside a
// padded allocation and is defined -- that is the §22.403 trap, and it is why the ground-truth ASan run for
// this CVE parses into an exact-size heap block.

struct buffer {
	const unsigned char *content;
	unsigned length;
	unsigned offset;
};

static int cannot_access_at_index(const struct buffer *b, unsigned index)
{
	return (b->offset + index) >= b->length;
}

static int parse_string(struct buffer *b)
{
	const unsigned char *p = b->content + b->offset;

	if (*p != '"')                   /* the dereference; `offset == length` reaches here */
		return 0;
	b->offset++;
	return 1;
}

int parse_object_vuln(const unsigned char *in, unsigned len)
{
	struct buffer b;
	int n = 0;
	unsigned i;

	unsigned char doc[4];

	if (len < 4)
		return -1;
	for (i = 0; i < 4; i++)
		doc[i] = in[i];
	b.content = doc;        /* EXACTLY as long as `b.length` says: an over-read is a real one */
	b.length = 4;
	b.offset = 0;

	for (i = 0; i < 4; i++) {
		if (cannot_access_at_index(&b, 0))
			break;
		if (b.content[b.offset] != ',') {
			b.offset++;
			continue;
		}
		b.offset++;              /* consume the comma ... */
		n += parse_string(&b);   /* CVE: ... and parse, with nothing after it */
	}
	return n;
}

int parse_object_fixed(const unsigned char *in, unsigned len)
{
	struct buffer b;
	int n = 0;
	unsigned i;

	unsigned char doc[4];

	if (len < 4)
		return -1;
	for (i = 0; i < 4; i++)
		doc[i] = in[i];
	b.content = doc;        /* EXACTLY as long as `b.length` says: an over-read is a real one */
	b.length = 4;
	b.offset = 0;

	for (i = 0; i < 4; i++) {
		if (cannot_access_at_index(&b, 0))
			break;
		if (b.content[b.offset] != ',') {
			b.offset++;
			continue;
		}
		if (cannot_access_at_index(&b, 1))   /* the fix: nothing comes after the comma */
			break;
		b.offset++;
		n += parse_string(&b);
	}
	return n;
}
