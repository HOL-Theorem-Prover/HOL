# --------------------------------
# Makefile for BVEC example
# --------------------------------

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

money:	money.o bddlib
	$(CPP) $(CFLAGS) money.o -o money -lbdd -lm

bddlib:
	cd ../../src; make

clean:
	rm -f *~
	rm -f *.o
	rm -f money

money.o:	../../src/bvec.h ../../src/fdd.h ../../src/bdd.h
