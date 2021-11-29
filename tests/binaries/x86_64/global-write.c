#include <unistd.h>

/*
 * This test performs a series of writes to a global variable to generate both
 * succeeding and failing goals.
 */

// Size of global array to allocate.
#define ARRAY_SIZE 8

// Offset in bytes between the start of `array` and the .text section.
#define TEXT_START_OFFSET -0x1000

char array[ARRAY_SIZE] = {0};

int main() {
  // In bounds write with concrete offset.  Generates 0 goals.
  array[0] = 1;

  // Write off the end of the .bss section.  Currently undetected (generates 0
  // goals), but should be detected in the future (expected to generate 1
  // failing goal)
  array[ARRAY_SIZE] = 2;

  // Write into text section.  Currently undetected (generates 0 goals), but
  // should be detected in the future (expected to generate 1 failing goal).
  array[TEXT_START_OFFSET] = 3;

  // Create but do not initialize a variable `i`.  The verifier will leave `i`
  // symbolic.
  ssize_t i;

  // Write `array` with an unconstrained symbolic index.  Generates 1 failing
  // goal.
  array[i] = 4;

  if (0 <= i && i < ARRAY_SIZE) {
    // Write `array` with in bounds symbolic index.  Generates 1 succeeding
    // goal.
    array[i] = 5;
  }

  if (TEXT_START_OFFSET <= i && i < ARRAY_SIZE) {
    // Write `array` with potentially out of bounds symbolic index.  This range
    // covers both the .text section and the .eh_frame section, neither of
    // which should be writable.  However, the verifier currently allows this.
    // Generates 1 succeeding goal (expected to generate 1 failing goal).
    array[i] = 6;
  }

  return 0;
}
