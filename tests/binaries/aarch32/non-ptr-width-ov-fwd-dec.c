#include <unistd.h>

#include "ambient_assert.h"

/*
 * A variant of non-ptr-width-ov.c that uses an override with a forward
 * declaration.
 */

char byte_id_2(char b) {
  return 0;
}

int main(void) {
  char x = 42;
  ambient_assert(byte_id_2(x) == x);
  return 0;
}

void _start(void) {
  main();
}
