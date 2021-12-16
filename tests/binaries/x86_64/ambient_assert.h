#pragma once

#include <stddef.h>

/*
 * The C ambient_assert does nothing.  It should be overriden to assert that
 * `assertion` is nonzero.
 */
void ambient_assert(size_t assertion);
