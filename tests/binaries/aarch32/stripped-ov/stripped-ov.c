#include "ambient_assert.h"

int f() {
  return 1;
}

int main() {
  ambient_assert(f() == 0);
  return 0;
}
