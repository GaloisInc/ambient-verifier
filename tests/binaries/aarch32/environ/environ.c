#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "ambient_assert.h"

extern char **environ;

// A naïve implementation of getenv.
char *getenv_naive(char *key) {
  size_t key_len = strlen(key);
  for (size_t i = 0; environ[i]; i++) {
    if (strncmp(key, environ[i], key_len) == 0) {
      size_t val_len = strlen(environ[i]) - key_len - 1;
      char *val = malloc(sizeof(char) * val_len + 1);
      memcpy(val, environ[i] + key_len + 1, val_len);
      val[val_len] = '\0';
      return val;
    }
  }
  return NULL;
}

int main(int argc, char *argv[]) {
  char *foo_val = getenv_naive("FOO");
  ambient_assert(memcmp(foo_val, "wombat", 7) == 0);
  char *bar_val = getenv_naive("BAR");
  ambient_assert(memcmp(bar_val, "koala", 6) == 0);
  char *baz_val = getenv_naive("BAZ");
  ambient_assert(memcmp(baz_val, baz_val, 5) == 0);
  ambient_assert(baz_val[5] == '\0');
  return 0;
}
