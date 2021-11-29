#include <stdlib.h>
#include <unistd.h>
#include <sys/syscall.h>

#define CALLOC_NUM 5

/**
 * This test verifies that the slab allocator places newly allocated memory
 * directly before previously allocated memory by writing off the end of one
 * allocation and into another, which alters control flow into an `execve`
 */

int main(void) {
  int* p1 = malloc(sizeof(int));
  int* p2 = calloc(CALLOC_NUM, sizeof(int));

  *p1 = 0;
  for (int i = 0; i <= CALLOC_NUM; ++i) {
    // write off end of p2 into p1
    p2[i] = i;
  }

  if (*p1) {
    syscall(SYS_execve, "/bin/sh", NULL, NULL);
  }

  return 0;
}

void _start(void) {
  main();
}
