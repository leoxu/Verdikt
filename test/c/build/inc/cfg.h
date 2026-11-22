#ifndef CFG_H
#define CFG_H
#define CAP (LIMIT + 8)          /* LIMIT comes from the Makefile's -DLIMIT=8: CAP is 16 */
#ifdef DEBUG_CHECKS
#define CHECKED 1
#else
#define CHECKED 0
#endif
#endif
