#include "ambient_assert.h"
#include "getone-static-function.h"

int main() {
  ambient_assert(getone() == 1);
  return 0;
}
