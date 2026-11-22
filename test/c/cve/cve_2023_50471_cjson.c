// CVE:    CVE-2023-50471
// SOURCE: cJSON cJSON.c:404 (cJSON_SetValuestring), fix adds the `object == NULL` test
// KIND:   null_deref
// VULN:   setvaluestring_obj_vuln
// FIXED:  setvaluestring_obj_fixed
//
//   -    if (!(object->type & cJSON_String) || (object->type & cJSON_IsReference))
//   +    if ((object == NULL) || !(object->type & cJSON_String) || ...
//
// `object` was dereferenced before being checked. The NULL is not planted: it is what
// `cJSON_GetObjectItem(root, "a")` returns for a field the attacker's document simply does not contain, and a
// caller updating a field it expects to exist passes that straight in. The fixture keeps that -- the lookup
// returns NULL for a document without the field -- because a fixture that passed a literal NULL would be
// testing a different, uninteresting program.

struct item {
	int type;
	char *valuestring;
};

#define TYPE_STRING   1
#define TYPE_IS_REF   2

static struct item g_doc[4];

static struct item *get_object_item(unsigned nfields, unsigned want)
{
	unsigned i;

	for (i = 0; i < nfields && i < 4; i++)
		if (i == want)
			return &g_doc[i];
	return 0;                        /* absent field -> NULL, as cJSON does */
}

int setvaluestring_obj_vuln(const unsigned char *in, unsigned caplen)
{
	struct item *target;
	unsigned nfields, want;

	if (caplen < 2)
		return -1;
	nfields = in[0] & 0x03;          /* how many fields the document has */
	want = in[1] & 0x03;             /* which one the caller asks for */
	g_doc[0].type = TYPE_STRING;
	g_doc[0].valuestring = 0;

	target = get_object_item(nfields, want);
	if (!(target->type & TYPE_STRING) || (target->type & TYPE_IS_REF))   /* CVE */
		return -2;
	return target->type;
}

int setvaluestring_obj_fixed(const unsigned char *in, unsigned caplen)
{
	struct item *target;
	unsigned nfields, want;

	if (caplen < 2)
		return -1;
	nfields = in[0] & 0x03;
	want = in[1] & 0x03;
	g_doc[0].type = TYPE_STRING;
	g_doc[0].valuestring = 0;

	target = get_object_item(nfields, want);
	if (target == 0)                 /* the fix */
		return -3;
	if (!(target->type & TYPE_STRING) || (target->type & TYPE_IS_REF))
		return -2;
	return target->type;
}
