#include "ambient_assert.h"

// On x86_64, there are six registers used for passing arguments.
int all_register_arguments(int a, int b, int c, int d, int e, int f) {
  return f;
}

// The last two arguments will be passed on the stack.
int way_too_many_arguments(int a, int b, int c, int d, int e, int f, int g, int h) {
  return h;
}

int main(void) {
  ambient_assert(all_register_arguments(1, 2, 3, 4, 5, 6) == 21);
  ambient_assert(way_too_many_arguments(1, 2, 3, 4, 5, 6, 7, 8) == 36);
  return 0;
}
