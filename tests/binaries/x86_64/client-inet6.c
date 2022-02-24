#include <arpa/inet.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <unistd.h>

/*
 * Test that the overrides for networking-related functions work as expected.
 * This program simulates a socket-based client that connects to a single
 * server and sends a message.
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
  server.sin6_addr = in6addr_any;
  server.sin6_port = htons(5000);
  int connect_rc = connect(sock_fd, (struct sockaddr *) &server, sizeof(server));
  if (connect_rc == -1) {
     return -1;
  }

  char buf[5] = "ABCD";
  int send_rc = send(sock_fd, buf, sizeof(buf), 0);
  if (send_rc == -1) {
    return -1;
  }
  // crucible-symio isn't quite sophisticated enough yet to simulate a server
  // that sends another message in response, so for now, we will stop here.

  close(sock_fd);

  you_win();

  return 0;
}
