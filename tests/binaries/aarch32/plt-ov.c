#include <unistd.h>

#include <sys/types.h>

/*
 * Test that the verifier can identify PLT stubs and dispatch overrides for
 * shared library functions.
 */

int main(void) {
  // The PLT stubs for these functions will be placed in .plt.  Unlike the
  // X86_64 tests, binding a function pointer to these will not result in the
  // stubs being placed in .plt.got.
  pid_t pid = getpid();
  pid_t ppid = getppid();

  return 0;
}
