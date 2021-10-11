#include <unistd.h>
#include <sys/syscall.h>

/*
 * This test assembles a ROP chain that hops from `clobber_ret` to `weird1` to
 * `weird2` to `weird3` to `execve`.  The verifier follows the chain and proves
 * that it ends in `execve`.  `../filesystems/rop-read/stdin` contains the
 * little endian binary representations of the addresses for `weird2`,
 * `weird3`, and `weird1` (in that order).
 */

// Size of the stack allocated array
#define ARRAY_SIZE 2

static void weird1() { }

static void weird2() { }

static void weird3() {
  execve("/bin/sh", NULL, NULL);
}

static void clobber_ret(void* array[]) {
  syscall(SYS_read, 0, array - 1, sizeof(void*));
}

int main(void) {
  void* array[ARRAY_SIZE];
  syscall(SYS_read, 0, array, ARRAY_SIZE * sizeof(void*));
  clobber_ret(array);
  return 0;
}

void _start(void) {
  main();
}
