.PHONY: all

all: $(patsubst %c,%exe,$(wildcard *.c))

CC=gcc
MUSL_CC=musl-gcc
STRIP=strip

# Syscall test needs the standard library available, so it builds with
# -nostartfiles instead of -nostdlib
syscall.exe: syscall.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

# This tests musl's implementation of _start, so we deliberately do not pass
# -nostartfiles here.
do-nothing.exe: do-nothing.c
	$(MUSL_CC) -static -no-pie $< -o $@

fsbase.exe: fsbase.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

rop.exe: rop.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

rop-read.exe: rop-read.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

read.exe: read.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

write.exe: write.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

open-close.exe: open-close.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

read-musl.exe: read-musl.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

read-symbolic-syscall-num.exe: read-symbolic-syscall-num.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

alloc.exe: alloc.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

crucible-syntax-function-ov.exe: crucible-syntax-function-ov.c ambient_assert.o
	$(CC) -nostartfiles -static -no-pie $^ -o $@

non-ptr-width-ov.exe: non-ptr-width-ov.c ambient_assert.o
	$(CC) -nostartfiles -static $^ -o $@

global-ov.exe: global-ov.c ambient_assert.o
	$(CC) -nostartfiles -static $^ -o $@

bv-typed-literal-ov.exe: bv-typed-literal-ov.c ambient_assert.o
	$(CC) -nostdlib -static -no-pie $^ -o $@

read-write-pointer-ov.exe: read-write-pointer-ov.c ambient_assert.o
	$(CC) -nostdlib -static -no-pie $^ -o $@

read-write-pointer-ov-pie.exe: read-write-pointer-ov.c ambient_assert.o
	$(CC) -nostdlib -pie $^ -o $@

ptr-diff-null-ov.exe: ptr-diff-null-ov.c ambient_assert.o
	$(CC) -nostdlib -static -no-pie $^ -o $@

just-exit-pie.exe: just-exit.c
	$(CC) -nostdlib -pie $^ -o $@

function-call-pie.exe: function-call.c
	$(CC) -nostartfiles -pie $^ -o $@

plt-ov.exe: plt-ov.c
	$(CC) -nostartfiles -pie $^ -o $@

plt-no-pltgot.exe: plt-no-pltgot.c
	$(CC) -nostartfiles -pie $^ -o $@

libfib.so: fib.o libgetone.so
	$(CC) -nostdlib -L./ -shared $< -lgetone -o $@

libgetone-stripped.so: libgetone.so
	$(STRIP) $< -o $@

so.exe: so.c libfib.so ambient_assert.o
	$(CC) -nostdlib -L./ so.c ambient_assert.o -lfib -lgetone -o $@

server-inet.exe: server-inet.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

server-inet6.exe: server-inet6.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

client-inet.exe: client-inet.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

client-inet6.exe: client-inet6.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

infinite-loop.exe: infinite-loop.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

infinite-recursion.exe: infinite-recursion.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

stripped-static.exe: stripped.c
	$(MUSL_CC) -static -no-pie $< -o $@
	$(STRIP) $@

stripped-dynamic.exe: stripped.c
	$(CC) -pie $< -o $@
	$(STRIP) $@

stripped-so.exe: stripped-so.c libgetone-stripped.so
	$(CC) -L./ stripped-so.c -lgetone-stripped -o $@
	$(STRIP) $@

main-args.exe: main-args.c ambient_assert.o
	$(CC) $^ -o $@

%.exe: %.c
	$(CC) -nostdlib -static -no-pie $< -o $@

%.o: %.c %.h
	$(CC) -nostdlib -c $<

lib%.so: %.o
	$(CC) -nostdlib -shared $^ -o $@
