#include "ambient_assert.h"

// On AArch32, there are four registers used for passing arguments.
int all_register_arguments(int a, int b, int c, int d) {
  return d;
}

// The last four arguments will be passed on the stack.
int way_too_many_arguments(int a, int b, int c, int d, int e, int f, int g, int h) {
  return h;
}

int main(void) {
  ambient_assert(all_register_arguments(1, 2, 3, 4) == 10);
  ambient_assert(way_too_many_arguments(1, 2, 3, 4, 5, 6, 7, 8) == 36);
  return 0;
}
