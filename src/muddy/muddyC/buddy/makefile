# ==============================================================
# Makefile for the BuDDy package
# - Do not touch. Edit "config" instead.
# ==============================================================

include config

# --------------------------------------------------------------
# The primary targets.
# --------------------------------------------------------------

buddy:
	cd src; make

docs:
	cd doc; make doc

install:
	cp -f src/libbdd.a $(LIBDIR)/libbdd.a
	chmod 644 $(LIBDIR)/libbdd.a
	cp -f src/bdd.h $(INCDIR)/bdd.h
	chmod 644 $(INCDIR)/bdd.h
	cp -f src/fdd.h $(INCDIR)/fdd.h
	chmod 644 $(INCDIR)/fdd.h
	cp -f src/bvec.h $(INCDIR)/bvec.h
	chmod 644 $(INCDIR)/bvec.h

uninstall:
	rm -f $(LIBDIR)/libbdd.a
	rm -f $(INCDIR)/bdd.h
	rm -f $(INCDIR)/fdd.h
	rm -f $(INCDIR)/bvec.h


# --------------------------------------------------------------
# Housekeeping
# --------------------------------------------------------------
TARGET = buddy
VERSION = 20
RD = $(TARGET)$(VERSION)

clean:
	cd examples/milner; make clean
	cd examples/cmilner; make clean
	cd examples/queen; make clean
	cd examples/adder; make clean
	cd examples/fdd; make clean
	cd examples/calculator; make clean
	cd examples/solitare; make clean
	cd examples/money; make clean
	cd src; make clean
	cd doc; make clean
	rm -f *~
	rm -f $(TARGET).tar.gz
	rm -f $(RD).tar.gz

examples: dummy
	cd examples/milner; make
	cd examples/cmilner; make
	cd examples/queen; make
	cd examples/adder; make
	cd examples/fdd; make
	cd examples/calculator; make
	cd examples/solitare; make
	cd examples/money; make

dummy:

backup:	clean
	tar -cvf $(TARGET).tar *
	gzip $(TARGET).tar

rel:	clean docs
	cd src; make depend
	mkdir $(RD)
	mkdir $(RD)/src
	mkdir $(RD)/doc
	mkdir $(RD)/examples
	cp config makefile README CHANGES $(RD)
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
	mkdir $(RD)/examples/solitare
	cp examples/solitare/* $(RD)/examples/solitare
	mkdir $(RD)/examples/money
	cp examples/money/* $(RD)/examples/money
	tar -cvf $(TARGET)$(VERSION).tar $(RD)/*
	gzip $(TARGET)$(VERSION).tar
	rm -fr $(RD)
	@cat RELEASE



