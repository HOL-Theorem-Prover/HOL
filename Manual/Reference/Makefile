# =====================================================================
# Makefile for the hol REFERENCE manual
# =====================================================================

PDFLATEX=pdflatex
DVILATEX=latex
MAKEINDEX=makeindex

# ---------------------------------------------------------------------
# Pathnames: Helpd = hol help directory, MAKEINDEX = makeindex program
# ---------------------------------------------------------------------
Helpd=../../help
D2TSED=bin/doc-to-tex.sed

HOLdir=../../
THMDIR=$(Helpd)/THEOREMS/
MAKEDOC=$(HOLdir)/Manual/Reference/bin/create-doc-files2

OTHER = ../LaTeX/commands.tex ../LaTeX/layout.sty ../LaTeX/ack.tex \
        ../LaTeX/ref-macros.tex

default: pdf
all: ps pdf
ps: reference.ps
pdf: reference.pdf

clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind *.toc \
         entries.tex theorems.tex reference.{ps,pdf}

reference.pdf: ids reference.tex $(OTHER)
	${PDFLATEX}  reference
	${MAKEINDEX} reference
	${PDFLATEX}  reference

reference.dvi: ids reference.tex $(OTHER)
	${DVILATEX}  reference
	${MAKEINDEX} reference
	${DVILATEX}  reference

reference.ps: reference.dvi
	dvips -Ppdf -G0 -f reference.dvi > reference.ps.tmp
	mv reference.ps.tmp $@

# Until we know how to generate the theorems that used to be part of the
# reference, we leave off the theorems entry that used to follow ids below
tex: ids
	@echo "TeX files made"

ids:
	@echo "\chapter{Pre-defined ML Identifiers}" > entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	$(Helpd)/src/Doc2Tex.exe ${Helpd}/Docfiles entries.tex

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
