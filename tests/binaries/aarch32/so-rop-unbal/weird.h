#pragma once

void weird1(void);

// Does nothing.  We need something to call here or GCC gets clever and doesn't
// link against libweird.
void do_nothing(void);
