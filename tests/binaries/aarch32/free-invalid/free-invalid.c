#include <stdlib.h>

int main(void) {
  // Double free
  int *x = malloc(sizeof(int));
  free(x);
  free(x);

  // Use after free
  int *y = malloc(sizeof(int));
  *y = 42;
  free(y);
  *y = 27;

  // free on pointer that doesn't point to the heap
  int wval = 42;
  int *w = &wval;
  free(w);

  return 0;
}
