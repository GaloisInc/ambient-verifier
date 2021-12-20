.PHONY: all

all: $(patsubst %c,%exe,$(wildcard *.c))

CC=gcc

# Syscall test needs the standard library available, so it builds with
# -nostartfiles instead of -nostdlib
syscall.exe: syscall.c
	$(CC) -nostartfiles -static $< -o $@

# This tests musl's implementation of _start, so we deliberately do not pass
# -nostartfiles here.
do-nothing.exe: do-nothing.c
	musl-gcc -static -no-pie $< -o $@

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

crucible-syntax-function-ov.exe: crucible-syntax-function-ov.c ambient_assert.o
	$(CC) -nostartfiles -static $^ -o $@

non-ptr-width-ov.exe: non-ptr-width-ov.c ambient_assert.o
	$(CC) -nostartfiles -static $^ -o $@

global-ov.exe: global-ov.c ambient_assert.o
	$(CC) -nostartfiles -static $^ -o $@

bv-typed-literal-ov.exe: bv-typed-literal-ov.c ambient_assert.o
	$(CC) -nostdlib -static $^ -o $@

read-write-pointer-ov.exe: read-write-pointer-ov.c ambient_assert.o
	$(CC) -nostdlib -static $^ -o $@

ptr-diff-null-ov.exe: ptr-diff-null-ov.c ambient_assert.o
	$(CC) -nostdlib -static $^ -o $@

%.exe: %.c
	$(CC) -nostdlib -static $< -o $@

%.o: %.c %.h
	$(CC) -nostdlib -c $<
