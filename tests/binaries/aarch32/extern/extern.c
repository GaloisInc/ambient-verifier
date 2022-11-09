#include "ambient_assert.h"

void f(void) {}

int g(void) {
  return 0;
}

int main(void) {
  f();
  int x = g();
  ambient_assert(x == 42);

  return 0;
}
