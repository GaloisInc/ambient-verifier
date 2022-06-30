#include <stdio.h>

#include "ambient_assert.h"

/*
 * A test for the `sprintf` override.  Tests the %s and %d directives with
 * concrete values.
 */

int main(void) {
  // First, test an invocation of sprintf where all of the arguments fit into
  // registers.
  const char* s = "test";
  const int i = 23;
  char out[32];
  sprintf(out, "%s%d", s, i);

  const char* expected = "test23";
  for (int i = 0; i < 6; ++i) {
    ambient_assert(out[i] == expected[i]);
  }

  // Next, test an invocation of sprintf where some of the arguments must be
  // spilled to memory.
  const int j = 4;
  const int k = 5;
  const int l = 6;
  const char* m = "78";
  const int n = 9;
  sprintf(out, "%s%d%d%d%d%s%d", s, i, j, k, l, m, n);

  const char* expected_spill = "test23456789";
  for (int i = 0; i < 12; ++i) {
    ambient_assert(out[i] == expected_spill[i]);
  }
  return 0;
}
