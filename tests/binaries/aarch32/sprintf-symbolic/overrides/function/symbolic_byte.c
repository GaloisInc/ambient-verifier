#include <crucible.h>

unsigned char symbolic_byte() {
  unsigned char b = fresh_uint8_t();
  assuming(b != '\0');
  return b;
}
