#include <unistd.h>
#include <sys/syscall.h>

/**
 * This test contains a buffer overrun resulting from a `read` syscall which
 * causes a change in control flow that the verifier detects with the weird
 * machine monitor
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
  syscall(SYS_read, 0, d.buf, 5);

  process_data(&d);
}

void _start(void) {
  main();
}
