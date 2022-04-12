#include <arpa/inet.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
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
  int sock_fd = socket(AF_INET6, SOCK_STREAM, 0);
  if (sock_fd == -1) {
     return -1;
  }

  struct sockaddr_in6 server;
  server.sin6_family = AF_INET6;
  // The line below generates 1 failing goal due to
  // https://github.com/GaloisInc/macaw/issues/266.
  server.sin6_addr = in6addr_any;
  // NB: the number 5000 becomes 34835 when converted from host byte order
  // to network byte order, which is why the corresponding directory in the
  // symbolic filesystem is
  // tests/filesystems/server-inet6/root/network/AF_INET6/SOCK_STREAM/34835.
  server.sin6_port = htons(5000);
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
