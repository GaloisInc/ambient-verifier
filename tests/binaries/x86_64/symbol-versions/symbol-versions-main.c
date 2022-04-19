#include "ambient_assert.h"

int bar();
int baz();

int main() {
  ambient_assert(bar() + baz() == 4);
  return 0;
}
