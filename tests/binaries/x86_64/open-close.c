#include <fcntl.h>
#include <unistd.h>
#include <sys/syscall.h>

/*
 * This is a smoke test that the `open` and `close` syscalls are connected and
 * can be strung together with a `read`.  Without a way to assert the contents
 * of memory it's hard to imagine a more rigorous test.  Once we have a way to
 * add custom assertions we should also improve this test.
 */

int main(void) {
  char c;
  const char path[] = "/open-me.txt";
  long fd = syscall(SYS_open, path, O_RDONLY);
  if (fd >= 0) {
    long read = syscall(SYS_read, fd, &c, 1);
    syscall(SYS_close, fd);
  }
  return (int)c;
}

void _start(void) {
  main();
}
