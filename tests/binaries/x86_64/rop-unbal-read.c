#ifndef AMBIENT_TARGET
#include <stdio.h>
#else
#include <unistd.h>
#include <sys/syscall.h>
#endif

char *bin_sh = "/bin/sh";

void artificial_gadget_1() {
  asm("pop %rsi; pop %rdx; ret");
}

void artificial_gadget_2() {
  asm("pop %rax; pop %rdi; ret");
}

void artificial_gadget_3() {
  asm("syscall;");
}

#ifndef AMBIENT_TARGET
void exploitable(FILE *fp) {
  char name[64];
  fread(name, 500, 1, fp);
  return;
}
#else
void exploitable(int fd) {
    char name[64];
    syscall(SYS_read, 0, name, 500);
    return;
}
#endif

#ifndef AMBIENT_TARGET
int main(int argc, char** argv) {
  FILE *fp = fopen(argv[1], "r");
  printf("I'm going to run this innocent function...\n");
  exploitable(fp);
  printf("I'm sure that was nothing!\n");
  return 0;
}
#else
int main(void) {
    int fd = 0;
    exploitable(fd);
    return 0;
}

void _start(void) {
    main();
}
#endif
