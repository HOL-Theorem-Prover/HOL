# =====================================================================
# Makefile for the string library documentation 
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the string help files
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

tex: ids theorems
	@echo "TeX files made"

ids:
	@echo "\chapter{ML Functions in the string Library}">entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/entries entries.tex

theorems:
	@echo "\chapter{Pre-proved Theorems}" > theorems.tex
	@echo "\input{theorems-intro}" >> theorems.tex
	@echo "\section{Definitions}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/defs theorems.tex
	@echo "\section{Theorems}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms theorems.tex

index: 
	${MAKEINDEX} string.idx index.tex

string: 
	latex string.tex 

all: 
	make clean; make tex; make string; make index; make string
