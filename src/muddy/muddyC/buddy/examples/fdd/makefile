# --------------------------------
# Makefile for FDD test example
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

statespace:	statespace.o bddlib
	$(CPP) $(CFLAGS) statespace.o -o statespace -lbdd -lm

bddlib:
	cd ../../src; make

clean:
	rm -f *~
	rm -f *.o
	rm -f statespace

statespace.o:	../../src/fdd.h
