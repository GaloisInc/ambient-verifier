#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/syscall.h>

int main() {
  const char *path = "/open-me.txt";
  long fd = syscall(SYS_open, path, O_RDONLY);
  return 0;
}
