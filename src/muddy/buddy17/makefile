# ==============================================================
# Makefile for the BuDDy package
# - Edit the lines below to configure
# ==============================================================

# --- Your compiler flags
CFLAGS = -O3 -W -Wtraditional -Wmissing-prototypes -Wall

# --- Where to install the library (directory, no trailing slash)
LIBDIR = /usr/local/lib

# --- Where to install the include file (directory, no trailing slash)
INCDIR = /usr/local/include

# --- Your C compiler
CC = gcc

# --- Your C++ compiler
CPP = g++

# Some machines are missing "CLOCKS_PER_SEC". Please define a default value
CLOCK=60


DFLAGS = -DDEFAULT_CLOCK=$(CLOCK)

# --------------------------------------------------------------
# The primary targets.
# --------------------------------------------------------------

buddy:
	cd src; make CC="$(CC)" CPP="$(CPP)" CFLAGS="$(CFLAGS)" \
	DFLAGS="$(DFLAGS)"

docs:
	cd doc; make doc

install:
	cp -f src/libbdd.a $(LIBDIR)/libbdd.a
	chmod 644 $(LIBDIR)/libbdd.a
	cp -f src/bdd.h $(INCDIR)/bdd.h
	chmod 644 $(INCDIR)/bdd.h

uninstall:
	rm -f $(LIBDIR)/libbdd.a
	rm -f $(INCDIR)/bdd.h


# --------------------------------------------------------------
# Housekeeping
# --------------------------------------------------------------
TARGET = buddy
VERSION = 17
RD = $(TARGET)$(VERSION)

clean:
	cd examples/adder && make clean
	cd src; make clean
	cd doc; make clean
	rm -f *~
	rm -f $(TARGET).tar.gz
	rm -f $(RD).tar.gz

backup:	clean
	tar -cvf $(TARGET).tar *
	gzip $(TARGET).tar

rel:	clean docs
	cd src; make depend
	mkdir $(RD)
	mkdir $(RD)/src
	mkdir $(RD)/doc
	mkdir $(RD)/examples
	cp makefile README CHANGES $(RD)
	./copysource $(RD)/src
	cp src/depend.inf src/makefile $(RD)/src
	cp doc/buddy.ps $(RD)/doc
	cp doc/bddnotes.ps $(RD)/doc
	cp doc/tech.txt $(RD)/doc
	echo "clean:" > $(RD)/doc/makefile
	mkdir $(RD)/examples/milner
	cp examples/milner/* $(RD)/examples/milner
	mkdir $(RD)/examples/cmilner
	cp examples/cmilner/* $(RD)/examples/cmilner
	mkdir $(RD)/examples/adder
	cp examples/adder/* $(RD)/examples/adder
	mkdir $(RD)/examples/queen
	cp examples/queen/* $(RD)/examples/queen
	mkdir $(RD)/examples/fdd
	cp examples/fdd/* $(RD)/examples/fdd
	mkdir $(RD)/examples/calculator
	mkdir $(RD)/examples/calculator/examples
	cp -R examples/calculator/* $(RD)/examples/calculator
	tar -cvf $(TARGET)$(VERSION).tar $(RD)/*
	gzip $(TARGET)$(VERSION).tar
	rm -fr $(RD)
	@cat RELEASE



