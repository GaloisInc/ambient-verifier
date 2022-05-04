#include <fcntl.h>
#include <unistd.h>
#include <sys/syscall.h>

#include "ambient_assert.h"

/*
 * This is a smoke test that the `open` and `close` syscalls are connected and
 * can be strung together with a `read`.
 */

int main(void) {
  char c;
  const char path[] = "/open-me.txt";
  long fd = syscall(SYS_open, path, O_RDONLY);
  if (fd >= 0) {
    long read = syscall(SYS_read, fd, &c, 1);

    // Assert that the correct byte was read from the concrete file
    ambient_assert(c == 'A');

    // Assert that 1 byte was read.  This is to ensure that the verifier
    // properly handles the return values from system calls.
    ambient_assert(read == 1);
    syscall(SYS_close, fd);
  }
  return (int)c;
}

void _start(void) {
  main();
}
