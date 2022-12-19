#include <unistd.h>

#include <sys/types.h>

/**
 * This tests that observable events properly capture override application,
 * including the correct arguments.  It uses overrides for `byte_id` and `padd`
 * with a combination of symbolic and concrete values.  It also performs an
 * ordinary function call to verify that the `FunctionCall` event still works as
 * expected.
*/

void call(void);
char byte_id(char);
static void* padd(const void*, size_t);

const int val = 0xF00D;

// Weird machine entrypoint
void wm(void) {
  // Test that the same non-overriden function called twice yields two
  // different function call events
  call();
  call();

  // Returns a symbolic value
  getpid();

  // Test that the same override called twice yields two different override
  // application events
  getpid();

  // Takes and returns a concrete value
  int res = byte_id(5);

  // Takes a concrete pointer and a concrete value.  Returns a concrete pointer.
  padd(&val, 16);
}

// Will be overriden
char byte_id(char) {
  return 0;
}

// Will be overriden
static void* padd(const void*,size_t) {
  return NULL;
}

// No-op call destination
void call(void) {

}

int main(void) {
  wm();
  return 0;
}
