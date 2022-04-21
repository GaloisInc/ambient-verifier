#include "../ambient_assert.h"

#include "export.h"
#include "reexport.h"

// This test checks that support for R_ARM_GLOB_DAT relocations is working as
// expected.  It read global variables both directly, and indirectly via a
// function in a different shared library.  It then sets the globals and reads
// them again.

int main(void) {
  ambient_assert(export_var == 0xdeadbeef);
  ambient_assert(export_var2 == 0xcafef00d);
  ambient_assert(get_export_var() == 0xdeadbeef);
  export_var = 0xf00d;
  export_var2 = 0xabc;
  ambient_assert(export_var == 0xf00d);
  ambient_assert(export_var2 == 0xabc);
  ambient_assert(get_export_var() == 0xf00d);
}

void _start(void) {
  main();
}
