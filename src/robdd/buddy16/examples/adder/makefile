# --------------------------------
# Makefile for adder test example
# --------------------------------

# --- Compiler flags
CFLAGS = -g -pedantic -Wall -ansi -L../../src -I../../src

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

adder:	adder.o bddlib
	$(CPP) $(CFLAGS) adder.o -o adder -lbdd -lm

bddlib:
	cd ../..; make

clean:
	rm -f *~
	rm -f *.o
	rm -f adder

adder.o:	../../src/bdd.h
