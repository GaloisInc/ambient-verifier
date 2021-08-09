#include <unistd.h>

// Size of the stack allocated array in bytes
#define ARRAY_SIZE 2

// An unconstrained symbolic write.  Generates successful and unsuccessful
// goals.
static void clobber_ret(void* array[]) {
  *(array - 1) = (void*)0x100;
};

int main(void) {
  void* array[ARRAY_SIZE] = {(void*)1, (void*)2};

  clobber_ret(array);

  return 0;
}

void _start(void) {
  main();
}
