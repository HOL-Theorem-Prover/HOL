###############################################################################
# Makefile for compiling HOL using MLton
# Created by Joe Hurd, October 2003
###############################################################################

.PHONY: all build clean reallyclean world depend

all: build test

build: bin/psl1

test: bin/psl1.out

clean:
	rm -f bin/psl*

reallyclean: clean
	rm -f Makefile.*

Makefile.src:
	scripts/deps.pl >Makefile.src

world: clean all

# Compiling to native code

MLPREP = scripts/milton.pl

UNQUOTE = ../../bin/unquote

MOSML2MLTON = scripts/mosml2mlton.pl

MLC = mlton -basis 1997 -verbose 2 -exn-history true

PRE = \
  pre/mosmllex/LexBuffer.sig pre/mosmllex/LexBuffer.sml \
  pre/Binaryset.sig pre/Binaryset.sml \
  pre/Binarymap.sig pre/Binarymap.sml \
  pre/Intset.sig pre/Intset.sml \
  pre/Intmap.sig pre/Intmap.sml \
  pre/PP.sig pre/PP.sml \
  pre/Random.sig pre/Random.sml \
  pre/Susp.sig pre/Susp.sml \
  pre/Listsort.sig pre/Listsort.sml \
  pre/MD5.sig pre/MD5.sml \
  pre/Polyhash.sig pre/Polyhash.sml \
  pre/Mosml2mlton.sml \
  ../../tools/Holmake/Systeml.sig ../../tools/Holmake/Systeml.sml

include Makefile.src

POST = src/std.prelude

# Evaluation of PSL formulas in the logic

Makefile.psl:
	scripts/deps.pl PSL ../../examples/PSL/regexp ../../examples/PSL/official-semantics ../../examples/PSL/executable-semantics >Makefile.psl

include Makefile.psl

PSL1 = ../../examples/PSL/executable-semantics/test

bin/psl1: bin/psl1.sml
	$(MLC) $+

bin/psl1.sml: $(PRE) $(SRC) $(PSL) $(POST) $(PSL1)
	@$(MLPREP) $+ | $(UNQUOTE) | $(MOSML2MLTON) >$@

bin/psl1.out: bin/psl1
	$+ | tee $@
