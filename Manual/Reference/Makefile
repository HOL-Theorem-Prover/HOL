# =====================================================================
# Makefile for the hol REFERENCE manual
# =====================================================================

# ---------------------------------------------------------------------
# Pathnames: Helpd = hol help directory, MAKEINDEX = makeindex program
# ---------------------------------------------------------------------
Helpd=../../help
MAKEINDEX=makeindex
D2TSED=bin/doc-to-tex.sed

HOLdir=../../
THMDIR=$(Helpd)/THEOREMS/
MAKEDOC=$(HOLdir)/Manual/Reference/bin/create-doc-files2

default:
	@echo "INSTRUCTIONS: Type \"make all\" to make REFERENCE"

#	@echo "   Type \"make thmdoc\" to make doc files for theorems"

clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind *.toc \
         entries.tex theorems.tex

# Until we know how to generate the theorems that used to be part of the
# reference, we leave off the theorems entry that used to follow ids below
tex: ids
	@echo "TeX files made"

ids:
	@echo "\chapter{Pre-defined ML Identifiers}" > entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/Docfiles entries.tex

theorems:
	@echo "\chapter{Pre-proved Theorems}" > theorems.tex
	@echo "\input{theorems-intro}" >> theorems.tex
	@echo "\section{Definitions of Basic Logical Constants}">>theorems.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/THEOREMS/basic-logic theorems.tex
	@echo "\section{Constants for syntactic abbreviations}" >> theorems.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/THEOREMS/syntax theorems.tex
	@echo "\section{Axioms}" >> theorems.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/THEOREMS/axioms theorems.tex
	@echo "\section{Logical tautologies}" >> theorems.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/THEOREMS/logic theorems.tex
	@echo "\section{Theorems about functions}" >> theorems.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/THEOREMS/functions theorems.tex
	@echo "\section{Theorems about the type {\tt one}}" >> theorems.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/THEOREMS/one theorems.tex
	@echo "\section{Theorems about combinators}" >> theorems.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/THEOREMS/combin theorems.tex
	@echo "\section{Theorems about pairs}" >> theorems.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/THEOREMS/pairs theorems.tex
	@echo "\section{Theorems about disjoint sums}" >> theorems.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/THEOREMS/sum theorems.tex
	@echo "\section{Theorems about arithmetic}" >> theorems.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/THEOREMS/arith theorems.tex
	@echo "\section{Theorems about lists}" >> theorems.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/THEOREMS/list theorems.tex
	@echo "\section{Theorems about trees}" >> theorems.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/THEOREMS/tree theorems.tex
	@echo "\section{Theorems used to define types}" >> theorems.tex
	/bin/sh bin/doc-to-tex ${D2TSED} ${Helpd}/THEOREMS/tydefs theorems.tex

reference:
	latex reference.tex

index:
	${MAKEINDEX}  reference.idx

all:
	make clean; make tex; make reference; make index; make reference

thmdoc:
	(cd $(THMDIR)axioms;    make thmdoc) ;
	(cd $(THMDIR)functions; $(MAKEDOC) fun) ;
	(cd $(THMDIR)one;       $(MAKEDOC) one) ;
	(cd $(THMDIR)combin;    $(MAKEDOC) combin) ;
	(cd $(THMDIR)sum;       $(MAKEDOC) sum) ;
	(cd $(THMDIR)arith;     $(MAKEDOC) num) ;
	(cd $(THMDIR)arith;     $(MAKEDOC) prim_rec) ;
	(cd $(THMDIR)arith;     $(MAKEDOC) arithmetic) ;
	(cd $(THMDIR)list;      $(MAKEDOC) list) ;
	(cd $(THMDIR)tree;      $(MAKEDOC) tree) ;
	(cd $(THMDIR)tree;      $(MAKEDOC) ltree) ;
	(cd $(THMDIR)tydefs;    $(MAKEDOC) tydefs) ;
	@echo "===> .doc files for theorems created"
