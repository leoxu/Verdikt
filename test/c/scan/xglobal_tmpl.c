// Shared "template" for xglobal_defs.c, included twice with different macros (the same X-macro idiom as
// xmacro_tmpl.c, but defining a *global variable* instead of a function - the shape that exposed a second,
// separate instance of the same underlying bug: freetype's ttdriver.c defines `tt_driver_class` this way
// (#include'd into truetype.c), and only ftinit.c, a different file, ever reads it under `--link`.
#ifdef TMPL_GUARD
int NS(helper)(void) { return LIMIT; }
const Rec NS(driver) = { LIMIT, NS(helper) };
#endif
