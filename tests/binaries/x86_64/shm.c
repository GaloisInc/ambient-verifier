#include <sys/ipc.h>
#include <sys/shm.h>

#include "ambient_assert.h"

// A test for the shmget and shmat overrides

int main(void) {
  // Allocate two shared memory segments
  int shm1 = shmget(IPC_PRIVATE, 32, 0);
  int shm2 = shmget(IPC_PRIVATE, 64, 0);
  ambient_assert(shm1 != shm2);

  // Get pointers to the underlying allocations
  int* p1 = shmat(shm1, NULL, 0);
  long* p2 = shmat(shm2, NULL, 0);

  // Write to the allocations
  *p1 = 12;
  *p2 = 13;
  ambient_assert(*p1 != *p2);

  // Calling shmget with a key other than IPC_PRIVATE should produce a failing
  // goal.
  shmget(32, 64, IPC_CREAT);

  // Calling shmat with a non-null shmaddr should produce a failing goal.
  int shm3 = shmget(IPC_PRIVATE, 128, 0);
  shmat(shm2, p1, 0);

  // Calling shmat with a nonexistent shmid should produce a failing goal.
  shmat(32, NULL, 0);
}

void _start(void) {
  main();
}
