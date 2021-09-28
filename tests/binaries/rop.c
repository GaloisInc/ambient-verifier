#include <unistd.h>
#include <sys/syscall.h>

/*
 * This test assembles a ROP chain that hops from `clobber_ret` to `weird1` to
 * `weird2` to `weird3` to `execve`.  The verifier follows the chain and proves
 * that it ends in `execve`.
 */

// Size of the stack allocated array
#define ARRAY_SIZE 2

static void weird1() { }

static void weird2() { }

static void weird3() {
  execve("/bin/sh", NULL, NULL);
}

static void clobber_ret(void* array[]) {
  *(array - 1) = (void*)&weird1;
}

int main(void) {
  void* array[ARRAY_SIZE] = {(void*)&weird2, (void*)&weird3};
  clobber_ret(array);
  return 0;
}

void _start(void) {
  main();
}
