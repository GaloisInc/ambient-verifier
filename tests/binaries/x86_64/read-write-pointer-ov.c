#include <unistd.h>

#include "ambient_assert.h"

/*
 * This test checks that the crucible syntax function override mechanism is
 * performing appropriately for pointer reads and writes.  It works by
 * overriding the broken `copy` function (which causes failing goals in the
 * caller by doing nothing) with a correct copy function that produces no such
 * goals.
 */

void copy(int* src, int* dest) {
  // Do nothing
}

int main(void) {
  int* res = NULL;

  int src = 1;
  int dst = 0;
  copy(&src, &dst);

  ambient_assert(dst == src);

  return 0;
}

void _start(void) {
  main();
}
