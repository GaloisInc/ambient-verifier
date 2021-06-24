.PHONY: all

all: $(patsubst %c,%exe,$(wildcard *.c))

CC=gcc

%.exe: %.c
	$(CC) -nostdlib -static $< -o $@
