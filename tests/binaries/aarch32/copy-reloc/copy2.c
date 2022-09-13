#include "ambient_assert.h"

extern int x;

int main() {
  ambient_assert(x == 42);
  return 0;
}
