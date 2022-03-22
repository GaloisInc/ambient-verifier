#include <stdbool.h>
#include <stdlib.h>
#include "ambient_assert.h"

/*
 * Test that simulation a main(argc, argv) function works as expected when the
 * user supplies command-line arguments.
 */

#define ARGC 3
#define ARGV0_LEN 9
#define ARGV1_LEN 2
#define ARGV2_LEN 2

const char expected_argv0[ARGV0_LEN] = "test.exe";
const char expected_argv1[ARGV1_LEN] = "a";
const char expected_argv2[ARGV2_LEN] = "b";

int main(int argc, char *argv[]) {
  const size_t expected_argv_lens[ARGC] = { ARGV0_LEN, ARGV1_LEN, ARGV2_LEN };
  const char *expected_argv[ARGC] = { expected_argv0, expected_argv1, expected_argv2 };

  bool b = (argc == ARGC);
  for (int i = 0; i < argc; i++) {
    for (int j = 0; j < expected_argv_lens[i]; j++) {
      b &= (argv[i][j] == expected_argv[i][j]);
    }
  }
  b &= (argv[argc] == NULL);

  ambient_assert(b);

  return 0;
}
