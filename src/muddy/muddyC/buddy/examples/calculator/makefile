# ---------------------------
# Makefile for BDD calculator
# ---------------------------

all: bddcalc

# --- Compiler flags
CFLAGS = -O3 -pedantic -Wall -ansi -L../../src -I../../src

# --- C++ compiler
CPP = g++

# --- C compiler
CC = gcc

# --- You may need to change these according to your flex and bison versions
parser.cxx:	parser.h parser.y
	  bison -d -o parser.cxx parser.y
	  mv parser.cxx.h tokens.h

lexer.cxx:	tokens.h parser.h lexer.l
	 flex -olexer.cxx lexer.l


# --- Do not touch ---

.SUFFIXES: .cxx .c

.cxx.o:
	$(CPP) $(CFLAGS) -c $<

.c.o:
	$(CC) $(CFLAGS) -c $<

bddcalc:	parser.o lexer.o hashtbl.o bddlib
	$(CPP) $(CFLAGS) parser.o lexer.o hashtbl.o -o bddcalc -lbdd -lm

bddlib:
	cd ../..; make

clean:
	rm -f *~ examples/*~
	rm -f *.o
	rm -f bddcalc parser.cxx lexer.cxx

# --- Needed for the author's Cygwin compiler
export BISONLIB=/cygnus/cygwin-b20/share/

