#include <stdio.h>

#include "ambient_assert.h"

/*
 * A test for the `sprintf` override.  Tests the %s and %d directives with
 * concrete values.
 */

int main(void) {
  const char* s = "test";
  const int i = 23;
  char out[32];
  sprintf(out, "%s%d", s, i);

  const char* expected = "test23";
  for (int i = 0; i < 6; ++i) {
    ambient_assert(out[i] == expected[i]);
  }
  return 0;
}
