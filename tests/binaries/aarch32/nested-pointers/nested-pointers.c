#include "ambient_assert.h"

void f(int **x) {}

int main() {
  int *x;
  f(&x);
  ambient_assert(*x == 42);
  return 0;
}
