# =====================================================================
# Makefile for the pred_set library documentation
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the pred_set help files
# ---------------------------------------------------------------------
Help=../help

.PHONY: index all clean


# ---------------------------------------------------------------------
# Pathname to the doc-to-tex script and doc-to-tex.sed file
# ---------------------------------------------------------------------
DOCTOTEXSH=../../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../../Manual/Reference/bin/doc-to-tex.sed
DOCTOTEX=/bin/sh ${DOCTOTEXSH} ${DOCTOTEXSED}
DOCTOTEXEXE=../../../help/src/Doc2Tex.exe

# ---------------------------------------------------------------------
# Pathname to the makeindex script
# ---------------------------------------------------------------------
#MAKEINDEX=../../../Manual/LaTeX/makeindex ../../../
MAKEINDEX=makeindex
default:
	@echo "INSTRUCTIONS: Type \"make all\" to make the documentation"

# ---------------------------------------------------------------------
# Remove all trace of previous LaTeX jobs
# ---------------------------------------------------------------------
clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ps *.pdf theorems.tex

tex: theorems ids
	@echo "TeX files made"

ids:
	@echo "\chapter{ML Functions in the Library}">entries.tex
	@echo "\label{entries}">>entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	${DOCTOTEXEXE} ${Help}/entries entries.tex

theorems:
	@echo "\chapter{Pre-proved Theorems}" > theorems.tex
	@echo "\input{theorems-intro}" >> theorems.tex
	@echo "\section{Membership, equality, and set specifications}">>theorems.tex
	cat ${Help}/thms/mem/*.doc >> theorems.tex
	@echo "\section{The empty and universal sets}">>theorems.tex
	${DOCTOTEX} ${Help}/thms/emuniv theorems.tex
	@echo "\section{Set inclusion}">>theorems.tex
	${DOCTOTEX} ${Help}/thms/subs theorems.tex
	@echo "\section{Intersection and union}">>theorems.tex
	${DOCTOTEX} ${Help}/thms/unin theorems.tex
	@echo "\section{Set difference}">>theorems.tex
	${DOCTOTEX} ${Help}/thms/diff theorems.tex
	@echo "\section{Disjoint sets}">>theorems.tex
	${DOCTOTEX} ${Help}/thms/disj theorems.tex
	@echo "\section{Insertion and deletion of an element}">>theorems.tex
	${DOCTOTEX} ${Help}/thms/insdel theorems.tex
	@echo "\section{The {\tt CHOICE} and {\tt REST} functions}">>theorems.tex
	${DOCTOTEX} ${Help}/thms/chre theorems.tex
	@echo "\section{Image of a function on a set}">>theorems.tex
	${DOCTOTEX} ${Help}/thms/image theorems.tex
	@echo "\section{Mappings between sets}">>theorems.tex
	${DOCTOTEX} ${Help}/thms/fun theorems.tex
	@echo "\section{Singleton sets}">>theorems.tex
	${DOCTOTEX} ${Help}/thms/sing theorems.tex
	@echo "\section{Finite and infinite sets}">>theorems.tex
	${DOCTOTEX} ${Help}/thms/fin theorems.tex
	@echo "\section{Cardinality of sets}">>theorems.tex
	${DOCTOTEX} ${Help}/thms/card theorems.tex

index:
	${MAKEINDEX} pred_set.idx

pred_set:
	latex pred_set.tex

ps:
	dvips pred_set.dvi -o

pdf:	pred_set.ps
	pdflatex pred_set.tex

all:
	make clean; make tex; make pred_set; make index; make pred_set ps pdf
