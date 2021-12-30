#include <sys/types.h>
#include <unistd.h>

#include "ambient_assert.h"

/*
 * This test checks that global variables in crucible syntax overrides are
 * working appropriately.  It calls a getpid override twice and asserts that
 * the symbolic values returned are equivalent.
 */

int main(void) {
  pid_t pid = getpid();

  // Same value is returned twice
  ambient_assert(pid == getpid());

  return 0;
}

void _start(void) {
  main();
}
