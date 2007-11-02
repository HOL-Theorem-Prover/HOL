# --------------------------------
# Makefile for solitare test example
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

solitare: solitare.o bddlib
	  $(CPP) $(CFLAGS) solitare.o -o solitare -lbdd -lm

bddlib:
	cd ../..; make

clean:
	rm -f *~
	rm -f *.o
	rm -f solitare

milner.o:	../../src/bdd.h
