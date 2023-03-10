.PHONY: all

all: $(patsubst %c,%exe,$(wildcard *.c))

CC=arm-linux-gnueabi-gcc
MUSL_CC=armv7m-linux-musleabi-gcc
STRIP=arm-linux-gnueabi-strip

# Syscall test needs the standard library available, so it builds with
# -nostartfiles instead of -nostdlib
syscall.exe: syscall.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

# This tests musl's implementation of _start, so we deliberately do not pass
# -nostartfiles here.
do-nothing.exe: do-nothing.c
	$(MUSL_CC) -static -no-pie -no-pie $< -o $@

do-nothing-pie.exe: do-nothing.c
	$(CC) -nostartfiles -pie $< -o $@

fsbase.exe: fsbase.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

rop.exe: rop.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

rop-unbal.exe: rop-unbal.c
	$(MUSL_CC) -g -nostartfiles -static -no-pie $< -o $@

rop-read.exe: rop-read.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

read.exe: read.c ambient_assert.o
	$(CC) -nostartfiles -static -no-pie $^ -o $@

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

crucible-syntax-function-ov.exe: crucible-syntax-function-ov.c
	$(CC) -nostartfiles -static -no-pie $< -o $@

non-ptr-width-ov.exe: non-ptr-width-ov.c ambient_assert.o
	$(CC) -nostartfiles -static $^ -o $@

non-ptr-width-ov-fwd-dec.exe: non-ptr-width-ov-fwd-dec.c ambient_assert.o
	$(CC) -nostartfiles -static $^ -o $@

bv-typed-literal-ov.exe: bv-typed-literal-ov.c ambient_assert.o
	$(CC) -nostdlib -static -no-pie $^ -o $@

ptr-diff-null-ov.exe: ptr-diff-null-ov.c ambient_assert.o
	$(CC) -nostdlib -static -no-pie $^ -o $@

ptr-diff-null-ov-pie.exe: ptr-diff-null-ov.c ambient_assert.o
	$(CC) -nostdlib -pie $^ -o $@

plt-ov.exe: plt-ov.c
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

so-rop-unbal/libweird.so: so-rop-unbal/weird.c
	$(CC) -nostartfiles -shared $< -o $@

so-rop-unbal/so-rop-unbal.exe: so-rop-unbal/so-rop-unbal.c so-rop-unbal/libweird.so
	$(CC) -nostartfiles -fno-stack-protector -Lso-rop-unbal/ -I./ so-rop-unbal/so-rop-unbal.c -lweird -o $@

so-static-function/libgetone-static-function.so: so-static-function/getone-static-function.c
	$(CC) -nostdlib -shared $< -o $@

so-static-function/so-static-function.exe: so-static-function/so-static-function.c so-static-function/libgetone-static-function.so ambient_assert.o
	$(CC) -nostdlib -Lso-static-function/ -I./ so-static-function/so-static-function.c ambient_assert.o -lgetone-static-function -o $@

relocations/reexport.o: relocations/reexport.c relocations/reexport.h
	$(CC) -nostdlib -c $< -o $@

relocations/libreexport.so: relocations/reexport.o relocations/libexport.so
	$(CC) -nostdlib -Lrelocations/ -shared $< -lexport -o $@

relocations/libexport.so: relocations/export.c
	$(CC) -nostdlib -shared $< -o $@

relocations/relocations.exe: relocations/relocations.c relocations/libreexport.so relocations/libexport.so
	$(CC) -nostdlib -Lrelocations/ -I./ relocations/relocations.c ambient_assert.o -lexport -lreexport -o $@

server-inet.exe: server-inet.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

server-inet6.exe: server-inet6.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

server-unix.exe: server-unix.c
	$(MUSL_CC) -static -no-pie $< -o $@

client-inet.exe: client-inet.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

client-inet6.exe: client-inet6.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

client-unix.exe: client-unix.c
	$(MUSL_CC) -static -no-pie $< -o $@

stripped-static.exe: stripped.c
	$(MUSL_CC) -static -no-pie $< -o $@
	$(STRIP) $@

stripped-dynamic.exe: stripped.c
	$(CC) -pie $< -o $@
	$(STRIP) $@

stripped-so/stripped-so.exe: stripped-so/stripped-so.c stripped-so/libgetone-stripped.so
	$(CC) -Lstripped-so/ -I./ stripped-so/stripped-so.c -lgetone-stripped -o $@
	$(STRIP) $@

stripped-ov/stripped-ov.exe: stripped-ov/stripped-ov.c ambient_assert.o
	$(MUSL_CC) -nostdlib -static -no-pie -I./ $^ -o $@
	$(STRIP) $@

main-args.exe: main-args.c ambient_assert.o
	$(CC) -no-pie $^ -o $@

symbol-versions/libsymbol-versions-bar.so: symbol-versions/symbol-versions-bar.c symbol-versions/symbol-versions-bar.map
	$(CC) symbol-versions/symbol-versions-bar.c -Wl,--version-script=symbol-versions/symbol-versions-bar.map -fpic -o $@ -shared

symbol-versions/libsymbol-versions-baz.so: symbol-versions/symbol-versions-baz.c symbol-versions/symbol-versions-baz.map
	$(CC) symbol-versions/symbol-versions-baz.c -Wl,--version-script=symbol-versions/symbol-versions-baz.map -fpic -o $@ -shared

symbol-versions/symbol-versions-main.exe: symbol-versions/symbol-versions-main.c symbol-versions/libsymbol-versions-bar.so symbol-versions/libsymbol-versions-baz.so ambient_assert.o
	$(CC) -Lsymbol-versions/ -I./ symbol-versions/symbol-versions-main.c ambient_assert.o -lsymbol-versions-bar -lsymbol-versions-baz -o $@

lookup-scope/liblookup-scope-a.so: lookup-scope/lookup-scope-a.c
	$(CC) -nostdlib $< -o $@ -shared

lookup-scope/liblookup-scope-b.so: lookup-scope/lookup-scope-b.c
	$(CC) -nostdlib $< -o $@ -shared

lookup-scope/lookup-scope.exe: lookup-scope/lookup-scope.c lookup-scope/liblookup-scope-a.so lookup-scope/liblookup-scope-b.so ambient_assert.o
	$(CC) -nostdlib -Llookup-scope/ -I./ lookup-scope/lookup-scope.c ambient_assert.o -llookup-scope-a -llookup-scope-b -o $@

shm.exe: shm.c ambient_assert.o
	$(MUSL_CC) -nostartfiles -static -no-pie $^ -o $@

shm-fwd-dec.exe: shm-fwd-dec.c ambient_assert.o
	$(MUSL_CC) -nostartfiles -static -no-pie $^ -o $@

printf-tailcall/printf-tailcall.exe: printf-tailcall/printf-tailcall.c
	$(MUSL_CC) -O2 -nostartfiles -no-pie $< -o $@

sprintf.exe: sprintf.c ambient_assert.o
	$(MUSL_CC) -nostartfiles -static $^ -o $@

strstr/strstr.exe: strstr/strstr.c ambient_assert.o
	$(MUSL_CC) -nostartfiles -static -no-pie -I. $^ -o $@

memcpy.exe: memcpy.c ambient_assert.o
	$(MUSL_CC) -static -nostartfiles -no-pie $^ -o $@

crucible-strings/crucible-strings.exe: crucible-strings/crucible-strings.c ambient_assert.o
	$(MUSL_CC) -nostartfiles -static -no-pie -I. $^ -o $@

weak-symbol/libweak-symbol-foo.so: weak-symbol/weak-symbol-foo.c
	$(CC) -nostdlib $< -o $@ -shared

weak-symbol/weak-symbol-main.exe: weak-symbol/weak-symbol-main.c weak-symbol/libweak-symbol-foo.so
	$(CC) -nostdlib -Lweak-symbol/ weak-symbol/weak-symbol-main.c -lweak-symbol-foo -o $@

way-too-many-arguments/way-too-many-arguments.exe: way-too-many-arguments/way-too-many-arguments.c ambient_assert.o
	$(MUSL_CC) -nostartfiles -static -no-pie -I. $^ -o $@

sscanf.exe: sscanf.c ambient_assert.o
	$(MUSL_CC) -nostartfiles -static -no-pie $^ -o $@

nested-pointers/nested-pointers.exe: nested-pointers/nested-pointers.c ambient_assert.o
	$(MUSL_CC) -nostartfiles -static -no-pie -I. $^ -o $@

startup-override/startup-override.exe: startup-override/startup-override.c ambient_assert.o
	$(MUSL_CC) -nostartfiles -static -no-pie -I. $^ -o $@

c-override/c-override.exe: c-override/c-override.c ambient_assert.o
	$(MUSL_CC) -nostartfiles -static -no-pie -I. $^ -o $@

nested-forward-decs/nested-forward-decs.exe: nested-forward-decs/nested-forward-decs.c ambient_assert.o
	$(MUSL_CC) -nostartfiles -static -no-pie -I. $^ -o $@

copy-reloc/libcopy1.so: copy-reloc/copy1.c
	$(CC) -nostdlib $< -o $@ -shared

copy-reloc/copy2.exe: copy-reloc/copy2.c copy-reloc/libcopy1.so ambient_assert.o
	$(CC) -nostdlib -Lcopy-reloc/ -I./ copy-reloc/copy2.c ambient_assert.o -lcopy1 -o $@

fd-zero.exe: fd-zero.c ambient_assert.o
	$(CC) -nostartfiles -no-pie -O $^ -o $@

null-check.exe: null-check.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

extern/extern.exe: extern/extern.c ambient_assert.o
	$(MUSL_CC) -nostartfiles -static -no-pie -I. $^ -o $@

getenv-symbolic/getenv-symbolic.exe: getenv-symbolic/getenv-symbolic.c ambient_assert.o
	$(MUSL_CC) -nostartfiles -static -no-pie -I. $^ -o $@

envp/envp.exe: envp/envp.c ambient_assert.h
	$(MUSL_CC) -nostartfiles -static -no-pie -I. $^ -o $@

environ/environ.exe: environ/environ.c ambient_assert.h
	$(MUSL_CC) -nostartfiles -static -no-pie -I. $^ -o $@

abs32-relative-reloc/libfoo.so: abs32-relative-reloc/foo.c
	$(CC) -nostdlib $< -o $@ -shared

abs32-relative-reloc/abs32-relative-reloc.exe: abs32-relative-reloc/abs32-relative-reloc.c abs32-relative-reloc/libfoo.so ambient_assert.o
	$(CC) -nostdlib -Labs32-relative-reloc/ -I./ abs32-relative-reloc/abs32-relative-reloc.c ambient_assert.o -lfoo -o $@

short-ov.exe: short-ov.c ambient_assert.o
	$(CC) -nostartfiles -static $^ -o $@

sprintf-symbolic/sprintf-symbolic.exe: sprintf-symbolic/sprintf-symbolic.c ambient_assert.o
	$(CC) -nostartfiles -static -no-pie -I. $^ -o $@

free-basic/free-basic.exe: free-basic/free-basic.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

free-invalid/free-invalid.exe: free-invalid/free-invalid.c
	$(MUSL_CC) -nostartfiles -static -no-pie $< -o $@

%.exe: %.c
	$(CC) -nostdlib -static -no-pie $< -o $@

%.o: %.c %.h
	$(CC) -nostdlib -c $<

lib%.so: %.o
	$(CC) -nostdlib -shared $^ -o $@
