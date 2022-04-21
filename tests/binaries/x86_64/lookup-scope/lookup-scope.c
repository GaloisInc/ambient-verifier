#include "ambient_assert.h"

char a();
char b();
char f();

int main() {
  ambient_assert(a() == 'a');
  ambient_assert(b() == 'b');
  ambient_assert(f() == a());
  return 0;
}
