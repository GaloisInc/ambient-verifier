#include <stdlib.h>

void you_win() {}

int main() {
  int *x = malloc(sizeof(int));
  if (x != NULL) {
    you_win();
  } else {
    // You lose
  }

  return 0;
}
