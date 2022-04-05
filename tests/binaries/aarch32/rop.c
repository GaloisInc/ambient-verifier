#include <unistd.h>
#include <sys/syscall.h>

#define ARRAY_SIZE 2

static void weird1() {
  execve("/bin/sh", NULL, NULL);
}

static void nop() {}

static void test(void) {
  void* array[ARRAY_SIZE];
  nop();
  array[3] = (void*)&weird1;
}

int main(void) {
  test();
  return 0;
}

void _start(void) {
  main();
}
