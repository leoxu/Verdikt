// ENTRY: serve
// EXPECT: bug tainted_sink
// SPEC: serve.yaml
// MODELS: libc
long recv(int fd, void *buf, unsigned long len, int flags);
char *strcpy(char *dst, const char *src);
int system(const char *cmd);
int serve(int fd) {
  char req[32];
  char cmd[64];
  long n = recv(fd, req, 31, 0);
  if (n < 0) return -1;
  req[n] = 0;
  strcpy(cmd, req);
  return system(cmd);
}
