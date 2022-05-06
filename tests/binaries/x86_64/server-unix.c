#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>

/*
 * Test that the overrides for networking-related functions work as expected.
 * This program simulates a socket-based server that connects to a single
 * client, receives a message, and sends it back.
 */

// If you've reached this point in the program, all of the networking-related
// overrides work as expected.
void you_win() {}

int main() {
  int sock_fd = socket(AF_UNIX, SOCK_STREAM, 0);
  if (sock_fd == -1) {
     return -1;
  }

  char path[18] = "/tmp/abc123def456";
  struct sockaddr_un server;
  server.sun_family = AF_UNIX;
  for (int i = 0; i < 18; i++) {
    server.sun_path[i] = path[i];
  }
  int bind_rc = bind(sock_fd, (struct sockaddr *) &server, sizeof(server));
  if (bind_rc == -1) {
     return -1;
  }

  int listen_rc = listen(sock_fd, 5);
  if (listen_rc == -1) {
    return -1;
  }

  int conn_fd = accept(sock_fd, NULL, NULL);
  if (conn_fd == -1) {
    return -1;
  }

  char buf[4];
  memset(buf, 0, sizeof(buf));
  int read_rc = recv(conn_fd, buf, sizeof(buf), 0);
  if (read_rc == -1) {
    return -1;
  }
  if (!(buf[0] == 'A' && buf[1] == 'B' && buf[2] == 'C' && buf[3] == 'D')) {
    return -1;
  }

  int send_rc = send(conn_fd, buf, sizeof(buf), 0);
  if (send_rc == -1) {
    return -1;
  }

  close(conn_fd);
  close(sock_fd);

  you_win();

  return 0;
}
