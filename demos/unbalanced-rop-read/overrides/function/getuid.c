#include "crucible.h"

// An override for getuid(2) that returns a symbolic value.  The override
// returns the same value for each subsequent call.
extern uid_t uid;
uid_t getuid() {
      return uid;
}
