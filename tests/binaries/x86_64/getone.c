#include "getone.h"

static int ONE = 1;

int getzero(void) {
  return 0;
}

int getone(void) {
  return ONE + getzero();
}
