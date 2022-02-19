#include <unistd.h>

#include <sys/types.h>

/*
 * Test that the verifier can identify PLT stubs and dispatch overrides for
 * shared library functions.
 */

int main(void) {
  // On ARM the creation of a getpid function pointer has no effect on whether
  // a stub for getpid is placed in .plt.got.  It is still placed in .plt.
  pid_t (*g)() = &getpid;
  pid_t pid = getpid();
  pid_t ppid = getppid();

  return 0;
}
