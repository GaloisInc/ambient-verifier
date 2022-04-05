#include <unistd.h>
#include <sys/syscall.h>

/*
 * This test assembles a ROP chain that hops from `clobber_ret` to `weird1` to
 * `weird2` to `execve`.  The verifier follows the chain and proves
 * that it ends in `execve`.  This test differs from `rop.c` in that it jumps
 * to the middle of `weird1` and `weird2` and therefore the stack is unbalanced
 * at the end of the function calls.
 */

// Size of the stack allocated array
#define ARRAY_SIZE 2

static void weird1() { }

static void weird2() {
  execve("/bin/sh", NULL, NULL);
}

static void clobber_ret(void* array[]) {
  *(array - 1) = (void*)&weird1 + 4;
}

int main(void) {
  void* array[ARRAY_SIZE] = {NULL, (void*)&weird2+4};
  clobber_ret(array);
  return 0;
}

void _start(void) {
  main();
}
