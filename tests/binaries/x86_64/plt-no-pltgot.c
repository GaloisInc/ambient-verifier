#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <sys/types.h>

/*
 * Test that the verifier can identify PLT stubs and dispatch overrides for
 * shared library functions.  This test differs from plt-ov.c in that it does
 * not generate a binary with a .plt.got section.
 */

int main(void) {
  // Only calling a function allows it to be bound lazily in .plt
  pid_t pid = getpid();
  pid_t ppid = getppid();

  return 0;
}
