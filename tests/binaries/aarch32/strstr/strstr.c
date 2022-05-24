#include <string.h>
#include "ambient_assert.h"

int main() {
  char *haystack = "ABC123";
  char *needle = "C12";
  char *res = strstr(haystack, needle);
  ambient_assert(res[0] == 'C' &&
                 res[1] == '1' &&
                 res[2] == '2' &&
                 res[3] == '3' &&
                 res[4] == '\0');
  return 0;
}
