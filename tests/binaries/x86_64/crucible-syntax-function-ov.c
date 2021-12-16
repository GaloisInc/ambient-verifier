#include <unistd.h>

#include "ambient_assert.h"

/*
 * This test checks that the crucible syntax function override mechanism is
 * performing appropriately.  It works by overriding the broken `padd` function
 * with a correct pointer addition function and asserting that the resulting
 * pointer is correctly calculated.
 */

char* padd(char* inp, size_t off) {
  return inp + (1024 * 1024 + 64);
}

int main(void) {
  char buf[5] = {0};
  char* res = padd(buf, 2);
  ambient_assert(res == (buf + 2));
  return 0;
}

void _start(void) {
  main();
}
