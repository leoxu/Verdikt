// The command line an initialiser is run with (DESIGN.md §22.380).
//
// `main` here is the project's initialiser, and like every server and QNX resource manager it reads its options
// before it sets anything up. Until the project states what those options are, the harness can only invent a
// command line -- and the one it invented, `argc = 1` with no options, is not a neutral choice: it is the claim
// that this program is started with no arguments. For a program whose options are MANDATORY that claim is false,
// the initialiser returns at its first check, every global keeps its static value, and the handler analysed
// afterwards is a vacuous safe. Measured on a real resource manager: `main` reached 18 of 1173 blocks.
#include <unistd.h>

static char gbuf[8];
static int gSeen;      // bit 1 = saw -c, bit 2 = saw -l, bit 4 = saw an option the string does not list
static char gFirst;    // first byte of -c's argument: proves the ARGUMENT was parsed, not just the letter

int main(int argc, char **argv) {
  int c;
  while ((c = getopt(argc, argv, "c:l:o:")) != -1) {
    switch (c) {
      case 'c': gSeen |= 1; gFirst = optarg ? optarg[0] : 0; break;
      case 'l': gSeen |= 2; break;
      case 'o': break;
      default:  gSeen |= 4; break;
    }
  }
  return 0;
}

int demo_argv_entry(unsigned idx) {
  // reachable only if getopt really parsed `-c 3 -l <path>`: both letters seen, neither unknown, and -c's
  // argument actually read. The unbounded index behind it is a real defect, and it is invisible until then.
  if (gSeen == 3 && gFirst == '3') return gbuf[idx];
  return -1;
}
