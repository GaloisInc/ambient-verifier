#include <stdint.h>
#include <string.h>

#include "ambient_assert.h"

/*
 * Test the memcpy override's ability to work with the lazy memory model by
 * passing it a string literal.
 */

struct s {
  uint16_t x;
  char y[108];
};

int main() {
  struct s ss;
  memset(&ss, 0, sizeof(ss));
  ss.x = 42;
  memcpy(ss.y, "Hello", 6);

  ambient_assert(ss.x == 42);
  char *expected = "Hello";
  for (int i = 0; i < 6; ++i) {
    ambient_assert(ss.y[i] == expected[i]);
  }

  return 0;
}
