void stop(const char *m);
void stop2(const char *m) __attribute__((noreturn));
static int tab[4];
int checked(int n) { if (n < 0 || n > 3) stop("bad index"); return tab[n]; }   /* guarded by a noreturn call */
int allstop(int n) { stop("always"); return tab[n + 100]; }                    /* every path ends in stop */
int attr(int n) { if (n != 1) stop2("attr"); return tab[n + 7]; }              /* real bug on n == 1 */
int plain(int n) { if (n == 7) { return tab[n]; } return 0; }
