# --------------------------------
# Makefile for milner test example
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

milner:	milner.o bddlib
	$(CPP) $(CFLAGS) milner.o -o milner -lbdd -lm

bddlib:
	cd ../../src; make

clean:
	rm -f *~
	rm -f *.o
	rm -f milner

milner.o:	../../src/bdd.h
