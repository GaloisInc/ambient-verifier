#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "ambient_assert.h"

// A naïve implementation of getenv that passes the environment variable
// array explicitly.
char *getenv_envp(char *key, char *envp[]) {
  size_t key_len = strlen(key);
  for (size_t i = 0; envp[i]; i++) {
    if (strncmp(key, envp[i], key_len) == 0) {
      size_t val_len = strlen(envp[i]) - key_len - 1;
      char *val = malloc(sizeof(char) * val_len + 1);
      memcpy(val, envp[i] + key_len + 1, val_len);
      val[val_len] = '\0';
      return val;
    }
  }
  return NULL;
}

int main(int argc, char *argv[], char *envp[]) {
  char *foo_val = getenv_envp("FOO", envp);
  ambient_assert(memcmp(foo_val, "wombat", 7) == 0);
  char *bar_val = getenv_envp("BAR", envp);
  ambient_assert(memcmp(bar_val, "koala", 6) == 0);
  char *baz_val = getenv_envp("BAZ", envp);
  ambient_assert(memcmp(baz_val, baz_val, 5) == 0);
  ambient_assert(baz_val[5] == '\0');
  return 0;
}
