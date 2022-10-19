#include <stdint.h>
#include <unistd.h>
#include <sys/syscall.h>

#include "weird.h"

/*
 * This test assembles a ROP chain that hops from `clobber_ret` to `weird1` to
 * `execve`.  The verifier follows the chain and proves that it ends in
 * `execve`.  This test differs from `rop-unbal.c` in that `weird1` is in a
 * shared library.
 */

// Size of the stack allocated array
#define ARRAY_SIZE 2

static void clobber_ret(uint32_t array[]) {
  array[3] = 0x10000184;
}

int main(void) {
  do_nothing();
  uint32_t array[ARRAY_SIZE] = {0};
  clobber_ret(array);
  return 0;
}

void _start(void) {
  main();
}
