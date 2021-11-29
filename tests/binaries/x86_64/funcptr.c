#include <stddef.h>

int buf[100];

struct Slab {
  int (*fptr)(int);
};


int f1(int x) {
  buf[1] = x;
  return x + 1;
}

int f2(int x) {
  buf[2] = x + 1;
  return x - 1;
}

void* malloc(size_t x) { return NULL; }

void g(int x, struct Slab *s) {
  s->fptr(x);
}

int main(void) {
  int x = 1;
  int stk[2];
  struct Slab * s = malloc(sizeof(struct Slab));
  s->fptr = &f1;
  buf[1] = x;
  stk[0] = buf[2];
  g(x, s);

  return 0;
}

void _start(void) {
  main();
}
