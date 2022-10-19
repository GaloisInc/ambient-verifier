#include <stddef.h>
#include <unistd.h>

#include "weird.h"

void weird1(void) {
  // Call execve.  We can't use the `execve` function because it will end up as
  // a PLT call to libc, but the weird machine executor does not currently
  // support PLT calls (see issue #163).
  asm("mov r7, #11");
  asm("swi #0");
}

void do_nothing(void) { }
