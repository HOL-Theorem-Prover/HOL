# ---------------------------------
# Makefile for N-queen test example
# ---------------------------------

# --- Compiler flags
CFLAGS = -O3 -pedantic -Wall -ansi -L../../src -I../../src

# --- C++ compiler
CPP = g++

# --- C compiler
CC = gcc


# --- Do not touch ---

.SUFFIXES: .cxx .c

.cxx.o:
	$(CPP) $(CFLAGS) -c $<

.c.o:
	$(CC) $(CFLAGS) -c $<

queen:	queen.o bddlib
	$(CPP) $(CFLAGS) queen.o -o queen -lbdd -lm

bddlib:
	cd ../..; make

clean:
	rm -f *~
	rm -f *.o
	rm -f queen

queen.o:	../../src/bdd.h

