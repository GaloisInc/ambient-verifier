#include <stdint.h>
#include "ambient_assert.h"

uint32_t x;
uint32_t *y;

int main() {
  ambient_assert(x == 42);
  ambient_assert(*y == 27);
  return 0;
}
