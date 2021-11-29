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

rop-read.exe: rop-read.c
	$(CC) -nostartfiles -static $< -o $@

read.exe: read.c
	$(CC) -nostartfiles -static $< -o $@

write.exe: write.c
	$(CC) -nostartfiles -static $< -o $@

open-close.exe: open-close.c
	$(CC) -nostartfiles -static $< -o $@

read-musl.exe: read-musl.c
	musl-gcc -nostartfiles -static $< -o $@

read-symbolic-syscall-num.exe: read-symbolic-syscall-num.c
	$(CC) -nostartfiles -static $< -o $@

alloc.exe: alloc.c
	musl-gcc -nostartfiles -static $< -o $@

crucible-syntax-function-ov.exe: crucible-syntax-function-ov.c
	$(CC) -nostartfiles -static $< -o $@

%.exe: %.c
	$(CC) -nostdlib -static $< -o $@
