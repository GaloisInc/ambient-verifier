#include "getone-static-function.h"

/*
 * This is almost identical to getone.c in the parent directory, except that
 * getzero is marked `static`.
 */

static int ONE = 1;

static int getzero(void) {
  return 0;
}

int getone(void) {
  return ONE + getzero();
}
