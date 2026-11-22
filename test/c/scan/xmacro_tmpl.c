// Shared "template" for xmacro_driver.c, included twice with different macros (the X-macro code-generation
// idiom, e.g. expat's xmltok.c pulling in xmltok_ns.c twice to generate `Xml*`/`Xml*NS` variant pairs). Each
// inclusion defines a differently-named, externally-linked function via the `NS()` macro; this file is never
// itself compiled as its own translation unit, so unlike a shared header its functions are not meant to be
// re-lowered out of every file that happens to include it - they belong to whichever file pastes them in.
#ifdef TMPL_GUARD
int NS(get_count)(void) { return LIMIT; }
#endif
