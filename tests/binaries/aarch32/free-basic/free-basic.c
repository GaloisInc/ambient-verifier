#include <stdlib.h>

int main(void) {
  int *x = malloc(sizeof(int));
  int *y = malloc(sizeof(int));
  int *z = malloc(sizeof(int));

  free(x);
  free(y);
  free(z);

  return 0;
}
