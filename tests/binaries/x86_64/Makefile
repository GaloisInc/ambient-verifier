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

rop-unbal.exe: rop-unbal.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

rop-unbal-read.exe: rop-unbal-read.c
	$(CC) -nostartfiles -no-pie -fno-stack-protector -fcf-protection=none -DAMBIENT_TARGET -g $< -o $@

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

so/libfib.so: fib.o so/libgetone.so
	$(CC) -nostdlib -Lso/ -shared $< -lgetone -o $@

so/libgetone.so: getone.c
	$(CC) -nostdlib -shared $< -o $@

stripped-so/libgetone-stripped.so: getone.c
	$(CC) -nostdlib -shared $< -o $@
	$(STRIP) $@

so/so.exe: so/so.c so/libfib.so ambient_assert.o
	$(CC) -nostdlib -Lso/ -I./ so/so.c ambient_assert.o -lfib -lgetone -o $@

so-static-function/libgetone-static-function.so: so-static-function/getone-static-function.c
	$(CC) -nostdlib -shared $< -o $@

so-static-function/so-static-function.exe: so-static-function/so-static-function.c so-static-function/libgetone-static-function.so ambient_assert.o
	$(CC) -nostdlib -Lso-static-function/ -I./ so-static-function/so-static-function.c ambient_assert.o -lgetone-static-function -o $@

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

stripped-so/stripped-so.exe: stripped-so/stripped-so.c stripped-so/libgetone-stripped.so
	$(CC) -Lstripped-so/ -I./ stripped-so/stripped-so.c -lgetone-stripped -o $@
	$(STRIP) $@

errno-glibc.exe: errno.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

errno-musl.exe: errno.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

main-args.exe: main-args.c ambient_assert.o
	$(CC) $^ -o $@

%.exe: %.c
	$(CC) -nostdlib -static -no-pie $< -o $@

%.o: %.c %.h
	$(CC) -nostdlib -c $<

lib%.so: %.o
	$(CC) -nostdlib -shared $^ -o $@
