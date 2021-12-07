#include <unistd.h>

/*
 * This test checks that the crucible syntax function override mechanism is
 * performing appropriately for bitvector literals with portable types.  It
 * works by overriding the broken `zero_size_t` function (which causes failing
 * goals in the caller by returning 1) with a correct function that always
 * returns 0 and produces no failing goals.
 */

size_t zero_size_t() {
  return 1;
}

int main(void) {
  size_t val = zero_size_t();
  int* nullptr = NULL;

  // NULL pointer dereference if val contains a nonzero value
  if (val) {
    return *nullptr;
  }
  return 0;
}

void _start(void) {
  main();
}
