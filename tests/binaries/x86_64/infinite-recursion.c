/*
 * A test for which simulation should not terminate unless a recursion bound
 * is imposed.
 */

void loop() {
  loop();
}

int main() {
  loop();
  return 0;
}
