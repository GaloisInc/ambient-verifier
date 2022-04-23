#include <unistd.h>
#include <sys/syscall.h>
#include <sys/types.h>

const char *bin_sh = "/bin/sh";

void artificial_gadget_1() {
  asm("pop %rsi; pop %rdx; ret");
}

void artificial_gadget_2() {
  asm("pop %rax; pop %rdi; ret");
}

void artificial_gadget_3() {
  asm("syscall; ret");
}

void exploitable_read(int fd) {
    char name[64];
    syscall(SYS_read, fd, name, 500);
    return;
}

void read_if_root(int fd) {
  if (isatty(fd)) {
    // `fd` cannot be a TTY
    return;
  }
  if (getuid() == 0) {
    // Must be root
    exploitable_read(fd);
  }
}

int main(void) {
    int fd = 0;
    if (getppid() == 1) {
      // Must be running under init
      read_if_root(fd);
    }
    return 0;
}

void _start(void) {
    main();
}
