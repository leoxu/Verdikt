// ENTRY: serve
// EXPECT: safe
// SPEC: serve.yaml
// MODELS: libc
long recv(int fd, void *buf, unsigned long len, int flags);
int system(const char *cmd);
int serve(int fd) {
  char req[32];
  long n = recv(fd, req, 31, 0);
  if (n < 0) return -1;
  return system("/bin/true");
}
