/**
 * This test doesn't look very interesting on its own, as it just calls a
 * function that does nothing. The part of this test that is actually
 * interesting is musl's implementation of _start that gets linked into the
 * binary, which is somewhat nontrivial. To make sure that the verifier is able
 * to handle musl's _start, we compile this code without -nostartfiles.
 */

void nothing(){}

int main() {
  nothing();
  return 0;
}
