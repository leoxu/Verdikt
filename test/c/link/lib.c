/* second translation unit: owns the data and the helpers */
int shared_cnt = 7;
int table[4] = {1, 2, 3, 4};
const char *msg = "hello";

static int counter = 100;
static int bump(int x) { return x + counter; }

int helper(int x) { return bump(x) * 2; }
int get_limit(void) { return 4; }
