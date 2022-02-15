#include <unistd.h>

// Size of the stack allocated array in bytes
#define ARRAY_SIZE 8

// A function that performs a symbolic write that is constrained to be in
// bounds.
static void symbolic_bounded(char* array) {
  size_t i;
  if (i <= ARRAY_SIZE) {
    array[i] = 3;
  }
}

// An unconstrained symbolic write.  Generates successful and unsuccessful
// goals.
static void symbolic_unbounded(char* array) {
  size_t i;
  array[i] = 2;

};

int main(void) {
  char array[ARRAY_SIZE] = {0};

  symbolic_bounded(array);
  symbolic_unbounded(array);

  return 0;
}

