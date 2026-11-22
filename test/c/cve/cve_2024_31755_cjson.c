// CVE:    CVE-2024-31755
// SOURCE: cJSON cJSON_SetValuestring(), fix 7e4d5da adds `|| valuestring == NULL`
// KIND:   null_deref
// VULN:   setvaluestring_arg_vuln
// FIXED:  setvaluestring_arg_fixed
//
//   -    if (object->valuestring == NULL)
//   +    if (object->valuestring == NULL || valuestring == NULL)
//          return NULL;
//        if (strlen(valuestring) <= strlen(object->valuestring))
//
// The function guarded the OBJECT's string against NULL but not the INCOMING one. This is a different NULL
// from CVE-2023-50471, which is `object` itself; both live in the same function, which is why both are kept.
//
// The NULL is produced by the document, not planted: the replacement value comes from another field of the
// SAME attacker-supplied document, and `cJSON_GetStringValue` returns NULL whenever that field is absent or
// is not a string.

struct item {
	int type;
	char *valuestring;
};

#define TYPE_STRING 1

static char g_a[8] = "aa";
static char g_b[8] = "bb";
static struct item g_doc[2];

static char *get_string_value(const struct item *it)
{
	if (it == 0 || !(it->type & TYPE_STRING))
		return 0;                        /* absent or not a string -> NULL */
	return it->valuestring;
}

static unsigned my_strlen(const char *s)
{
	unsigned n = 0;

	while (s[n])
		n++;
	return n;
}

int setvaluestring_arg_vuln(const unsigned char *in, unsigned caplen)
{
	struct item *target;
	char *newval;

	if (caplen < 1)
		return -1;
	g_doc[0].type = TYPE_STRING;
	g_doc[0].valuestring = g_a;
	g_doc[1].type = (in[0] & 1) ? TYPE_STRING : 0;   /* field "b" may not be a string */
	g_doc[1].valuestring = g_b;

	target = &g_doc[0];
	newval = get_string_value(&g_doc[1]);
	if (target->valuestring == 0)                    /* CVE: only the object's string is checked */
		return -2;
	return (int)my_strlen(newval);                   /* strlen(NULL) */
}

int setvaluestring_arg_fixed(const unsigned char *in, unsigned caplen)
{
	struct item *target;
	char *newval;

	if (caplen < 1)
		return -1;
	g_doc[0].type = TYPE_STRING;
	g_doc[0].valuestring = g_a;
	g_doc[1].type = (in[0] & 1) ? TYPE_STRING : 0;
	g_doc[1].valuestring = g_b;

	target = &g_doc[0];
	newval = get_string_value(&g_doc[1]);
	if (target->valuestring == 0 || newval == 0)     /* the fix */
		return -2;
	return (int)my_strlen(newval);
}
