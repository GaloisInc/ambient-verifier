#include <unistd.h>
#include <sys/syscall.h>

#define ARRAY_SIZE 8

int main(void) {
  char array[ARRAY_SIZE];

  // getppid returns an unconstrained symbolic value
  pid_t pid = getppid();

  if (0 <= pid && pid < ARRAY_SIZE) {
    // In bounds write.  Generates 2 passing goals.
    array[pid] = 1;
  }

  // Potentially out of bounds write.  Generates 2 failing goals.
  array[pid] = 2;

  return 0;
}

void _start(void) {
  main();
}
