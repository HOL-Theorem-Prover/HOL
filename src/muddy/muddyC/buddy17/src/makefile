# ==============================================================
# Makefile for BDD source
# ==============================================================

# --- full object list
OBJ = bddio.o bddop.o bvec.o cache.o fdd.o kernel.o \
      pairs.o reorder.o tree.o
CFILES = bddio.c bddop.c bvec.c cache.c fdd.c kernel.c \
       pairs.c reorder.c tree.c
CCFILES = cppext.cxx
HFILES = bdd.h fdd.h bvec.h


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

libbdd.a:	$(OBJ)
	ar r libbdd.a $(OBJ)
	ranlib libbdd.a

clean:
	rm -f lib$(TARGET).a
	rm -f *.o core *~ scrap*

depend:
	gcc -MM $(CFLAGS) $(DFLAGS) $(CFILES) > depend.inf
	g++ -MM $(CFLAGS) $(DFLAGS) $(CCFILES) >> depend.inf

###
include depend.inf
