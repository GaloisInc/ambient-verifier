#include <unistd.h>
#include <sys/syscall.h>

/**
 * This test verifies that the `write` syscall is connected. We don't currently
 * have a great way to verify that it works (the underlying machinery is tested
 * in crucible-symio and crucible-llvm), so we are mostly just testing that the
 * syscall number mapping is correct (i.e., the verifier should not error out
 * when it hits the syscall).
 */

char buf[100];

int main(void) {
  // Write to stdout
  syscall(SYS_write, 1, buf, 1);
}

void _start(void) {
  main();
}
