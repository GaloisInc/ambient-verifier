#include <stdio.h>
#include "ambient_assert.h"

int arg1;
int arg2;
char arg3[4];
char arg4[4];

void assert_string_eq(char a[4], char b[4]) {
  for (int i = 0; i < 4; i++) {
    ambient_assert(a[i] == b[i]);
  }
}

int main() {
  sscanf("123 z abc 3fg", "%d %c %s %s", &arg1, &arg2, arg3, arg4);
  ambient_assert(arg1 == 123);
  ambient_assert(arg2 == 'z');
  assert_string_eq(arg3, "abc");
  assert_string_eq(arg4, "3fg");

  return 0;
}
