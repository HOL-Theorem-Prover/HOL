# ==============================================================
# Makefile for BDD source
# - Do not touch
# ==============================================================

# --- full object list
OBJ = bddio.o bddop.o bvec.o cache.o fdd.o imatrix.o kernel.o \
      pairs.o prime.o reorder.o tree.o
CFILES = bddio.c bddop.c bvec.c cache.c fdd.c imatrix.c kernel.c \
       pairs.c prime.c reorder.c tree.c
CCFILES = cppext.cxx

include ../config

# --------------------------------------------------------------
# Code generation
# --------------------------------------------------------------

.SUFFIXES: .cxx .c

.cxx.o:
	$(CPP) $(CFLAGS) $(DFLAGS) -c $<

.c.o:
	$(CC) $(CFLAGS) $(DFLAGS) -c $<


# --------------------------------------------------------------
# The primary targets.
# --------------------------------------------------------------

libbdd.a:	$(OBJ) ../config
	ar r libbdd.a $(OBJ)
	ranlib libbdd.a

clean:
	rm -f lib$(TARGET).a
	rm -f *.o core *~
#	rm -f libbdd.a
	rm -f libbdd.a
	rm -f bddtest


depend:
	gcc -MM $(CFLAGS) $(DFLAGS) $(CFILES) > depend.inf
	g++ -MM $(CFLAGS) $(DFLAGS) $(CCFILES) >> depend.inf

bddtest: libbdd.a bddtest.cxx ../config
	$(CPP) $(CFLAGS) $(DFLAGS) bddtest.cxx -o bddtest -L. -lbdd
###
include depend.inf
