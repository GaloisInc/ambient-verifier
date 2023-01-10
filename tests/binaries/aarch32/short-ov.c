#include <unistd.h>

#include "ambient_assert.h"

/*
 * This test checks that override mechanisms are working properly for function
 * overrides with 16-bit arguments and return values.
 */

short short_id(short s) {
  return 0;
}

short short_id_fwd(short s) {
  return 0;
}

short getppid_fwd(void) {
  return 0;
}

void exit_fwd(short s) { }

int main(void) {
  short x = 42;

  // Test crucible syntax override taking short as input and returning a short
  ambient_assert(short_id(x) == x);

  // Test crucible syntax override wrapping another crucible syntax override
  // taking and returning a short
  ambient_assert(short_id_fwd(x) == x);

  // Test crucible syntax override wrapping Haskell override and truncating
  // return to a short
  getppid_fwd();

  // Test crucible syntax override wrapping Haskell override and expanding a
  // short to an int.  This call should result in a failed goal from a non-zero
  // exit code.
  exit_fwd(x);

  return 0;
}

void _start(void) {
  main();
}
