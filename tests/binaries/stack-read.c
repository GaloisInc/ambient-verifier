#include <unistd.h>

/*
 * This test performs a series of reads on the stack to generate both
 * succeeding and failing goals.
 */

// Size of the stack allocated array in bytes
#define ARRAY_SIZE 8

// An array index that is out of bounds for the array, but still on the stack
#define ARRAY_OUT_OF_BOUNDS 1024

// An array index that is out of bounds for the stack
#define STACK_OUT_OF_BOUNDS 1024 * 1024 + 64

int main(void) {
  char array[ARRAY_SIZE] = {0};
  char val;

  // In bounds read with concrete index.  Generates 0 goals.
  val = array[0];

  // Read `array` with a concrete index that is out of bounds for `array`,
  // but in bounds for the stack.  Generates 0 goals.
  val += array[ARRAY_OUT_OF_BOUNDS];

  // Read `array` with a concrete index that is out of bounds for the stack.
  // Generates 2 failing goals.
  val += array[STACK_OUT_OF_BOUNDS];

  // Create but do not initialize a variable `i`.  The verifier will leave `i`
  // symbolic.
  size_t i;

  // Read array with unconstrained symbolic index.  Generates 2 failing goals.
  val += array[i];

  if (i < ARRAY_SIZE) {
    // Read array with symbolic index constrained to be in bounds.  Generates
    // 2 successful goals.
    val += array[i];
  }

  if (i <= ARRAY_OUT_OF_BOUNDS) {
    // Read array with symbolic index that may be out of bounds for `array`,
    // but is in bounds for the stack.  Generates 2 successful goals.
    val += array[i];
  }
  return (int)val;
}
