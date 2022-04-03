#include "ambient_assert.h"
#include "fib.h"

int main(void) {
  ambient_assert(fib(6) == 8);
  return 0;
}

void _start(void) {
  main();
}
