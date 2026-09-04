CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra -std=c99 -fopenmp
SRCS    := $(wildcard src/*.c)

lin: $(SRCS) src/lin.h
	$(CC) $(CFLAGS) -o $@ $(SRCS) -ldl

test: lin
	sh test/run.sh

clean:
	rm -f lin

.PHONY: test clean
