#include <unistd.h>

#include "ambient_assert.h"

/*
 * This test checks that override mechanisms are working properly for function
 * overrides with arguments and return values that are different in width from
 * pointers.  It does so using a `byte_id` function that takes `char` as input
 * and (in the crucible syntax override) returns the same value back.
 */

char byte_id(char b) {
  return 0;
}

int main(void) {
  char x = 42;
  ambient_assert(byte_id(x) == x);
  return 0;
}

void _start(void) {
  main();
}
