# =====================================================================
# Makefile for the pred_sets library documentation 
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the pred_sets help files
# ---------------------------------------------------------------------
Help=../help

# ---------------------------------------------------------------------
# Pathname to the doc-to-tex script and doc-to-tex.sed file 
# ---------------------------------------------------------------------
DOCTOTEX=../../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../../Manual/Reference/bin/doc-to-tex.sed

# ---------------------------------------------------------------------
# Pathname to the makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=../../../Manual/LaTeX/makeindex ../../../
default:
	@echo "INSTRUCTIONS: Type \"make all\" to make the documentation"

# ---------------------------------------------------------------------
# Remove all trace of previous LaTeX jobs
# ---------------------------------------------------------------------
clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg
	@echo "\begin{theindex}" > index.tex
	@echo "\mbox{}" >> index.tex
	@echo "\end{theindex}" >> index.tex

tex: theorems ids
	@echo "TeX files made"

ids:
	@echo "\chapter{ML Functions in the Library}">entries.tex
	@echo "\label{entries}">>entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/entries entries.tex

theorems:
	@echo "\chapter{Pre-proved Theorems}" > theorems.tex
	@echo "\input{theorems-intro}" >> theorems.tex
	@echo "\section{Membership, equality, and set specifications}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/mem theorems.tex
	@echo "\section{The empty and universal sets}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/emuniv theorems.tex
	@echo "\section{Set inclusion}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/subs theorems.tex
	@echo "\section{Intersection and union}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/unin theorems.tex
	@echo "\section{Set difference}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/diff theorems.tex
	@echo "\section{Disjoint sets}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/disj theorems.tex
	@echo "\section{Insertion and deletion of an element}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/insdel theorems.tex
	@echo "\section{The {\tt CHOICE} and {\tt REST} functions}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/chre theorems.tex
	@echo "\section{Image of a function on a set}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/image theorems.tex
	@echo "\section{Mappings between sets}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/fun theorems.tex
	@echo "\section{Singleton sets}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/sing theorems.tex
	@echo "\section{Finite and infinite sets}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/fin theorems.tex
	@echo "\section{Cardinality of sets}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/card theorems.tex

index: 
	${MAKEINDEX} pred_sets.idx index.tex

pred_sets: 
	latex pred_sets.tex 

all: 
	make clean; make tex; make pred_sets; make index; make pred_sets

