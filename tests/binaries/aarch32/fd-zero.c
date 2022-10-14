#include <stdio.h>
#include <sys/select.h>
#include "ambient_assert.h"

int main(int argc, char *argv[]) {
  fd_set rfds;
  FD_ZERO(&rfds);
  // We use `argc` here to ensure that the assembly loop arising from the line
  // above doesn't get optimized away.
  ambient_assert(FD_ISSET(argc, &rfds) == 0);

  return 0;
}
