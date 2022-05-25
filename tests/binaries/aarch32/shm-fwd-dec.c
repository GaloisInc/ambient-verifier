#include <sys/ipc.h>
#include <sys/shm.h>

#include "ambient_assert.h"

// A test that invokes shmget() by way of an override with a
// forward declaration.

// This should be overridden.
int shmget_ipc_private(void) {
  return 0;
}

int main(void) {
  int shmid = shmget_ipc_private();
  int *p1 = shmat(shmid, NULL, 0);
  int *p2 = shmat(shmid, NULL, 0);
  *p1 = 10;
  ambient_assert(*p1 == *p2);
  return 0;
}
