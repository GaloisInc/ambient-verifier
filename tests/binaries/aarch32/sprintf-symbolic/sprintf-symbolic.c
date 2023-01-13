#include <stdio.h>
#include "ambient_assert.h"

unsigned char symbolic_byte() {
  return 0;
}

int main(void) {
  char out[4];
  int arg1 = (int)(symbolic_byte());
  char arg2[3] = { symbolic_byte(), symbolic_byte(), '\0' };
  sprintf(out, "%d%s", arg1, arg2);

  ambient_assert(out[0] == '?');
  int tmp;
  if (out[1] > 1) {
    if (out[2] > 2) {
      tmp = 5;
    } else {
      tmp = 6;
    }
  } else {
    if (out[2] > 2) {
      tmp = 7;
    } else {
      tmp = 8;
    }
  }
  ambient_assert(tmp > 4);

  return 0;
}
