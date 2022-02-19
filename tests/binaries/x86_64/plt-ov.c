#include <stdlib.h>
#include <unistd.h>

#include <sys/types.h>

/*
 * Test that the verifier can identify PLT stubs and dispatch overrides for
 * shared library functions.
 */

int main(void) {
  // Creating function pointers forces functions into .plt.got as they can no
  // longer be bound lazily
  void* (*m)(size_t) = &malloc;
  void* (*c)(size_t, size_t) = &calloc;

  int* x = malloc(sizeof(int));
  int* y = calloc(sizeof(int), 1);

  // Only calling a function allows it to be bound lazily in .plt
  pid_t pid = getpid();
  pid_t ppid = getppid();

  return 0;
}
