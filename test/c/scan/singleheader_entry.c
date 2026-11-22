// Drives singleheader_lib.h the way a real consumer of an stb-style single-header library does: #define the
// implementation macro, then #include the header. See scan_tests.cpp "single-header library" test.
#define SINGLEHEADER_IMPLEMENTATION
#include "singleheader_lib.h"
