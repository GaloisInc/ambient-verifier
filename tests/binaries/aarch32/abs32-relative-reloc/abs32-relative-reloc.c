#include "ambient_assert.h"

extern char f();

int main() {
  ambient_assert(f() == 'H');
  return 0;
}
