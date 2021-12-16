#include <unistd.h>

#include "ambient_assert.h"

/*
 * This test checks that the `ptr-diff` and `make-null` extension wrappers work
 * as expected.  It uses the `checked_ptr_diff` override (which contains calls
 * to `ptr-diff` and `make-null`) and checks that the result is as expected.
 */

size_t checked_ptr_diff(char* ptr1, char* ptr2) {
  return 1;
}

int main(void) {
  char pointee = 'A';
  char* p1 = &pointee + 3;
  char* p2 = &pointee;

  ambient_assert(checked_ptr_diff(p1, p2) == 3);
  ambient_assert(checked_ptr_diff(NULL, p2) == 0);
  ambient_assert(checked_ptr_diff(p1, NULL) == 0);
  return 0;
}

void _start(void) {
  main();
}
