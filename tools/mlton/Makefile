###############################################################################
# Makefile for compiling HOL using MLton
# Created by Joe Hurd, October 2003
###############################################################################

.PHONY: all clean reallyclean world

all: basic metis psl netsem

clean:
	rm -f bin/basic* bin/metis* bin/psl* bin/netsem*

reallyclean: clean
	rm -f Makefile.*

Makefile.src:
	scripts/deps.pl >Makefile.src

world: clean all

# Compiling to native code

MOSMLC = mosmlc -standalone -I ../../sigobj

MLPREP = scripts/milton.pl

UNQUOTE = ../../bin/unquote
UNQUOTE = cat

MOSML2MLTON = scripts/mosml2mlton.pl

MLC = mlton -basis 1997 -verbose 3

PRE = \
  pre/LexBuffer.sig                pre/LexBuffer.sml                \
  pre/Binaryset.sig                pre/Binaryset.sml                \
  pre/Binarymap.sig                pre/Binarymap.sml                \
  pre/Intset.sig                   pre/Intset.sml                   \
  pre/Intmap.sig                   pre/Intmap.sml                   \
  pre/PP.sig                       pre/PP.sml                       \
  pre/Random.sig                   pre/Random.sml                   \
  pre/Susp.sig                     pre/Susp.sml                     \
  pre/Listsort.sig                 pre/Listsort.sml                 \
  pre/MD5.sig                      pre/MD5.sml                      \
  pre/Polyhash.sig                 pre/Polyhash.sml                 \
                                   pre/Mosml2mlton.sml              \
  ../../tools/Holmake/Systeml.sig  ../../tools/Holmake/Systeml.sml

include Makefile.src

PRELUDE = src/std.prelude

# Basic HOL tests

basic: bin/basic1.out bin/basic2.out

Makefile.basic:
	scripts/deps.pl BASIC ../../src/portableML ../../src/experimental-kernel ../../src/parse ../../src/bool ../../src/goalstack >Makefile.basic

include Makefile.basic

BASIC1 = test/basic-test1.sml

bin/basic1: bin/basic1.sml
	$(MLC) $+

bin/basic1.sml: $(PRE) $(BASIC) $(PRELUDE) $(BASIC1)
	@$(MLPREP) $+ | $(UNQUOTE) | $(MOSML2MLTON) >$@
	wc $@

bin/basic1.out: bin/basic1
	$+ | tee $@

BASIC2 = test/basic-test2.sml

bin/basic2: bin/basic2.sml
	$(MLC) $+

bin/basic2.sml: $(PRE) $(BASIC) $(PRELUDE) $(BASIC2)
	@$(MLPREP) $+ | $(UNQUOTE) | $(MOSML2MLTON) >$@
	wc $@

bin/basic2.out: bin/basic2
	$+ | tee $@

# Metis

metis: bin/metis-test.out bin/metis-tptp bin/metis-itptp

Makefile.metis:
	scripts/deps.pl METIS_SRC ../../src/portableML ../../src/experimental-kernel ../../src/parse ../../src/bool ../../src/goalstack ../../src/taut ../../src/compute/src ../../src/q ../../src/combin ../../src/marker ../../src/labels ../../src/lite ../../src/refute ../../src/simp/src ../../src/metis >Makefile.metis
	scripts/deps.pl METIS_THEORIES ../../src/meson/src ../../src/basicProof ../../src/relation ../../src/pair/src ../../src/sum ../../src/one ../../src/option ../../src/num/theories ../../src/num/reduce/src ../../src/num/arith/src ../../src/num ../../src/IndDef ../../src/datatype/parse ../../src/datatype/equiv ../../src/datatype/record ../../src/datatype ../../src/list/src ../../src/tfl/src ../../src/unwind ../../src/boss ../../src/llist ../../src/pred_set/src >>Makefile.metis

include Makefile.metis

METIS_TEST = test/mlibProblem.sig test/mlibProblem.sml test/metis-test.sml

bin/metis-test.sml: $(PRE) $(METIS_SRC) $(METIS_THEORIES) $(PRELUDE) $(METIS_TEST)
	@$(MLPREP) $+ | $(UNQUOTE) | $(MOSML2MLTON) >$@
	wc $@

bin/metis-test: bin/metis-test.sml
	$(MLC) $+

bin/metis-test.out: bin/metis-test
	$+ | tee $@

METIS_TPTP = test/metis-tptp.sml

bin/metis-tptp.sml: $(PRE) $(METIS_SRC) $(METIS_TPTP)
	@$(MLPREP) $+ | $(UNQUOTE) | $(MOSML2MLTON) >$@
	wc $@

bin/metis-tptp: bin/metis-tptp.sml
	$(MLC) $+

bin/metis-itptp: $(METIS_TPTP)
	$(MOSMLC) -o $@ -toplevel $(METIS_TPTP)

# PSL formulas

psl: bin/psl.out

Makefile.psl:
	scripts/deps.pl PSL ../../examples/PSL/regexp ../../examples/PSL/path ../../examples/PSL/1.01/official-semantics ../../examples/PSL/1.01/executable-semantics >Makefile.psl

include Makefile.psl

PSL = ../../examples/PSL/1.01/executable-semantics/test

bin/psl.sml: $(PRE) $(SRC) $(PSL) $(PRELUDE) $(PSL)
	@$(MLPREP) $+ | $(UNQUOTE) | $(MOSML2MLTON) >$@

bin/psl: bin/psl.sml
	$(MLC) $+

bin/psl.out: bin/psl
	$+ | tee $@

# Checking TCP traces with netsem

netsem: bin/netsem

Makefile.netsem:
	scripts/deps.pl NETSEM_SRC ../../src/portableML ../../src/experimental-kernel ../../src/parse ../../src/bool ../../src/goalstack ../../src/taut ../../src/compute/src ../../src/q ../../src/combin ../../src/marker ../../src/labels ../../src/lite ../../src/refute ../../src/simp/src ../../src/metis ../../src/meson/src ../../src/basicProof ../../src/relation ../../src/pair/src ../../src/sum ../../src/one ../../src/option ../../src/num/theories ../../src/num/reduce/src ../../src/num/arith/src ../../src/num ../../src/IndDef ../../src/datatype/parse ../../src/datatype/equiv ../../src/datatype/record ../../src/datatype ../../src/list/src ../../src/tfl/src ../../src/unwind ../../src/boss ../../src/n_bit ../../src/string ../../src/pred_set/src ../../src/ring/src ../../src/integer ../../src/finite_map ../../src/hol88 ../../src/real ../../src/bag >Makefile.netsem
	scripts/deps.pl NETSEM netsem >>Makefile.netsem

include Makefile.netsem

bin/netsem.sml: $(PRE) $(NETSEM_SRC) $(NETSEM)
	@wc $(PRE)
	@echo
	@wc $(NETSEM_SRC)
	@echo
	@wc $(NETSEM)
	@echo
	@$(MLPREP) $+ | $(UNQUOTE) | $(MOSML2MLTON) >$@

bin/netsem: bin/netsem.sml
	$(MLC) $+
