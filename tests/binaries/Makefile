.PHONY: all

all: $(patsubst %c,%exe,$(wildcard *.c))

CC=gcc

# Syscall test needs the standard library available, so it builds with
# -nostartfiles instead of -nostdlib
syscall.exe: syscall.c
	$(CC) -nostartfiles -static $< -o $@

fsbase.exe: fsbase.c
	$(CC) -nostartfiles -static $< -o $@

rop.exe: rop.c
	$(CC) -nostartfiles -static $< -o $@

read.exe: read.c
	$(CC) -nostartfiles -static $< -o $@

%.exe: %.c
	$(CC) -nostdlib -static $< -o $@
