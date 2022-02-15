#include <unistd.h>

/*
 * This test performs a series of reads to a global variable. Out-of-bounds reads
 * should generate failing goals.
 */

// Size of global array to allocate in bytes.
#define ARRAY_SIZE 8

// Offset in bytes between the start of `array` and the .text section.
#define TEXT_START_OFFSET -0x1000

char array[ARRAY_SIZE] = {0};

int main(void) {
  char val;

  // In bounds read with a concrete index.  Generates 0 goals.
  val = array[0];

  // Read off the end of the .bss section.  Currently undetected (generates 0
  // goals), but could be detected in the future depending on whether we
  // believe this kind of read is likely to crash programs.
  val += array[ARRAY_SIZE];

  // Read from text section.  This is generally legal.  Generates 0 goals.
  val += array[TEXT_START_OFFSET];

  // Create but do not initialize a variable `i`.  The verifier will leave `i`
  // symbolic.
  ssize_t i;

  // Read `array` with an unconstrained symbolic index.  Generates 1 failing
  // goal.
  val += array[i];

  if (0 <= i && i < ARRAY_SIZE) {
    // Read `array` with in bounds symbolic index.
    val += array[i];
  }

  if (TEXT_START_OFFSET <= i && i < ARRAY_SIZE) {
    // Read `array` with potentially out of bounds symbolic index.  This range
    // covers both the .text section and the .eh_frame section, both of which
    // are readable.  However, this range may contain unmapped memory segments
    // in practice.  Currently the verifier generates no goals for
    // this case, but we should consider whether that's appropriate.
    val += array[i];
  }

  return (int)val;
}
