#include <stdlib.h>
#include "ambient_assert.h"

int main(void) {
  char *symbolic_val = getenv("SYMBOLIC");

  for (int i = 0; i < 2; i++) {
    char symbolic_char = symbolic_val[i];
    ambient_assert(symbolic_char || !(symbolic_char));
    ambient_assert(symbolic_char == symbolic_char);
  }
  ambient_assert(symbolic_val[2] == '\0');

  return 0;
}
