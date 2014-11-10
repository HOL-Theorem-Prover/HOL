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
DOCTOTEXEXE=../../../help/src/Doc2Tex.exe

# ---------------------------------------------------------------------
# Pathname to the makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=makeindex

default:
	@echo "INSTRUCTIONS: Type \"make all\" to make the documentation"

# ---------------------------------------------------------------------
# Remove all trace of previous LaTeX jobs
# ---------------------------------------------------------------------
clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind \
              entries.tex theorems.tex string.ps string.pdf

tex: ids theorems
	@echo "TeX files made"

ids:
	@echo "\chapter{ML Functions in the string Library}">entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	${DOCTOTEXEXE} ${Help}/entries entries.tex

theorems:
	@echo "\chapter{Pre-proved Theorems}" > theorems.tex
	@echo "\input{theorems-intro}" >> theorems.tex
	@echo "\section{Theorems}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms theorems.tex

index:
	${MAKEINDEX} string.idx

string:
	latex string.tex

ps:
	dvips string.dvi -o

pdf:	string.ps
	pdflatex string.tex

all:
	make clean; make tex; make string; make index; make string ps pdf
