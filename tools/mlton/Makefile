###############################################################################
# Makefile for compiling HOL using MLton
# Created by Joe Hurd, October 2003
###############################################################################

.PHONY: all clean reallyclean world depend

all: basic metis psl

clean:
	rm -f bin/basic* bin/metis* bin/psl*

reallyclean: clean
	rm -f Makefile.*

Makefile.src:
	scripts/deps.pl >Makefile.src

world: clean all

# Compiling to native code

MLPREP = scripts/milton.pl

UNQUOTE = ../../bin/unquote

MOSML2MLTON = scripts/mosml2mlton.pl

MLC = mlton -basis 1997 -verbose 3

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

# Basic HOL tests

basic: bin/basic1.out

Makefile.basic:
	scripts/deps.pl BASIC ../../src/portableML ../../src/experimental-kernel ../../src/parse ../../src/bool ../../src/goalstack >Makefile.basic

include Makefile.basic

BASIC1 = test/basic-test1.sml

bin/basic1: bin/basic1.sml
	$(MLC) $+

bin/basic1.sml: $(PRE) $(BASIC) $(POST) $(BASIC1)
	@$(MLPREP) $+ | $(UNQUOTE) | $(MOSML2MLTON) >$@
	wc $@

bin/basic1.out: bin/basic1
	$+ | tee $@

# Metis test problems

metis: bin/metis1.out

Makefile.metis:
	scripts/deps.pl METIS ../../src/portableML ../../src/experimental-kernel ../../src/parse ../../src/bool ../../src/goalstack ../../src/taut ../../src/compute/src ../../src/q ../../src/combin ../../src/marker ../../src/labels ../../src/lite ../../src/refute ../../src/simp/src ../../src/metis ../../src/meson/src ../../src/basicProof ../../src/relation ../../src/pair/src ../../src/sum ../../src/one ../../src/option ../../src/num/theories ../../src/num/reduce/src ../../src/num/arith/src ../../src/num ../../src/IndDef ../../src/datatype/parse ../../src/datatype/equiv ../../src/datatype/record ../../src/datatype ../../src/list/src ../../src/tfl/src ../../src/unwind ../../src/boss ../../src/llist ../../src/pred_set/src >Makefile.metis

include Makefile.metis

METIS1 = test/mlibProblem.sig test/mlibProblem.sml test/metis-test.sml

bin/metis1: bin/metis1.sml
	$(MLC) $+

bin/metis1.sml: $(PRE) $(METIS) $(POST) $(METIS1)
	@$(MLPREP) $+ | $(UNQUOTE) | $(MOSML2MLTON) >$@
	wc $@

bin/metis1.out: bin/metis1
	$+ | tee $@

# PSL formulas

psl: bin/psl1.out

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
