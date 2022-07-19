#include <stdio.h>

/*
 * A test for the `sprintf` override with a stack buffer overflow to a gadget.
 *
 * Should have 1 failed goal for the nonzero exit code from the gadget.
 */

void artificial_gadget() {
    // Load exit code into %rdi
    asm("mov $0x2, %rdi");
    // Load exit syscall number into %rax
    asm("mov $0x3c, %rax");
    // Make the system call
    asm("syscall;");
}

// Payload overwrites the return from `exploitable`.  The values in the first
// 40 bytes pad out from the `out` buffer to the storred return value.  The
// values themselves are mostly unimportant, but they extend beyond the
// traditional ASCII range to ensure that the sprintf override isn't
// interpreting them as UTF-8 (or any other encoding for that matter).
const char payload[] = {
    0xe8, 0xcc, 0x9d, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
    0x22, 0xcc, 0x9d, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
    0xd0, 0xcf, 0x9d, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
    0xf2, 0xbf, 0xb4, 0xb3, 0xf2, 0xae, 0xb5, 0xdd,
    0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
    0x35, 0x11, 0x40, /* artificial_gadget address */
    0
};

void exploitable(void) {
  char out[20];
  sprintf(out, "%s", payload);
}

int main(void) {
  exploitable();
  return 0;
}
