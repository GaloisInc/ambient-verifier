#include <unistd.h>

/*
 * This test performs a series of reads to a global variable to generate both
 * succeeding and failing goals.
 */

// Size of global array to allocate in bytes.
#define ARRAY_SIZE 8

// Offset in bytes between the start of `array` and the .text section.
#define TEXT_START_OFFSET -0x100DC

char array[ARRAY_SIZE] = {0};

int main(void) {
  char val;

  // In bounds read with a concrete index.  Generates 2 successful goals.
  val = array[0];

  // Read off the end of the .bss section.  Generates 1 successful and 1
  // failing goal.
  val += array[ARRAY_SIZE];

  // Read from text section.  This is generally legal.  Generates 2 successful
  // goals.
  val += array[TEXT_START_OFFSET];

  // Create but do not initialize a variable `i`.  The verifier will leave `i`
  // symbolic.
  ssize_t i;

  // Read `array` with an unconstrained symbolic index.  Generates 2 failing
  // goals.
  val += array[i];

  if (0 <= i && i < ARRAY_SIZE) {
    // Read `array` with in bounds symbolic index.  Generates 2 successful
    // goals.
    val += array[i];
  }

  if (TEXT_START_OFFSET <= i && i < ARRAY_SIZE) {
    // Read `array` with potentially out of bounds symbolic index.  This range
    // covers from the .text section through the array.  While the text section
    // is readable, this range contains also unmapped memory segments and the
    // verifier generates 3 successful goals and 1 failing goal.
    val += array[i];
  }

  return (int)val;
}
