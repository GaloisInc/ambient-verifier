#include "crucible.h"

// An override for getppid(2) that returns a symbolic value.  The override
// returns a new symbolic value each time to represent the fact that the parent
// PID can change at any time.
pid_t getppid() {
      return fresh_pid_t();
}
