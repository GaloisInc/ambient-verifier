#include <stdlib.h>
#include "ambient_assert.h"

int f(const char *x) {
  return 0;
}

void g(char *x) {}

int main() {
  ambient_assert(f("hello") == 1);
  ambient_assert(f("world!") == 2);
  ambient_assert(f("turbo-wombat") == 3);

  char *c = malloc(sizeof(char) * 6);
  g(c);
  ambient_assert(f(c) == 1);
  return 0;
}
