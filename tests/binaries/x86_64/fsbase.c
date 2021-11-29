#include <unistd.h>
#include <sys/syscall.h>

#define ARRAY_ELEMENTS 8

int main(void) {
  // Allocate array in thread local storage
  static __thread int array[ARRAY_ELEMENTS];

  // In bounds write.  Generates no goals.
  array[0] = 2;

  // Write out of bounds for array, but still in TLS bounds.  Generates no
  // goals.
  array[ARRAY_ELEMENTS] = 3;

  // Write out of bounds of TLS.  Generates 2 failing goals.
  array[1024] = 4;

  // Exit syscall writes errno.  Generates no goals.
  syscall(SYS_exit, 0);

  return 0;
}

void _start(void) {
  main();
}
