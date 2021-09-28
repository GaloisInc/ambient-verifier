#include <unistd.h>
#include <sys/syscall.h>

/**
 * This is a variant of read.c which relies on the syscall number being a
 * symbolic value. This serves as a regression test for issue #17.
 *
 * While the concrete read test has 1 expected failing goal (for failing to
 * reach an execve), the symbolic test has 2 expected failing goals:
 * 1. for failing to reach an execve, and
 * 2. for having branches that do not reach the weird machine.
 */

// Use a struct to force the `trusted` flag to be placed in memory immediately
// after the buffer
typedef struct {
  // Data buffer
  char buf[4];
  // Flag indicating whether the data in `buf` is trusted (system controlled)
  // or untrusted (user controlled)
  int trusted;
} data;

void unsafe_process(const data* d) {
  // Process trusted data in a privileged way
}

void safe_process(const data* d) {
  // Safely process untrusted data
}

void process_data(const data* d) {
  if (d->trusted) {
    unsafe_process(d);
  } else {
    safe_process(d);
  }
}

int main(void) {
  data d;
  d.trusted = 0;

  // Off-by-one read overflows into d.trusted
  long syscall_number;
  if (syscall_number == SYS_read) {
    syscall(syscall_number, 0, d.buf, 5);
  }

  process_data(&d);
}

void _start(void) {
  main();
}
