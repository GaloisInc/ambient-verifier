#include <unistd.h>

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

  if (dst == 1) {
    res = &dst;
  };

  // NULL pointer dereference if copy failed
  return *res;
}

void _start(void) {
  main();
}
