#include "crucible.h"

// An override for isatty(2) that returns a symbolic value. Result is either 0
// or 1.
int isatty(void) {
      const int res = fresh_int();

      assuming(res == 0 || res == 1);

      return res;
}
