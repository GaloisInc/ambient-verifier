#include <unistd.h>

/*
 * This test checks that the crucible syntax function override mechanism is
 * performing appropriately.  It works by overriding the broken `padd` function
 * (which causes failing goals in the caller by returning an out-of-bounds
 * pointer) with a correct pointer addition function that produces no such
 * goals.
 */

char* padd(char* inp, size_t off) {
  return inp + (1024 * 1024 + 64);
}

int main(void) {
  char buf[5] = {0};
  char* res = padd(buf, 2);
  return *res;
}

void _start(void) {
  main();
}
