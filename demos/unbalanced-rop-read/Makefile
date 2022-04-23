MUSL_CC=musl-gcc

rop-unbal-read.exe: rop-unbal-read.c
	$(MUSL_CC) -nostartfiles -static -no-pie -fno-stack-protector -fcf-protection=none -g $< -o $@
