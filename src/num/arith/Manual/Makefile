# =====================================================================
# Makefile for the arith library documentation
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the arith help files
# ---------------------------------------------------------------------
Help=../help

# ---------------------------------------------------------------------
# Pathname to the doc-to-tex script and doc-to-tex.sed file
# ---------------------------------------------------------------------
DOCTOTEXEXE=../../../../help/src/Doc2Tex.exe

# ---------------------------------------------------------------------
# Pathname to the makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=makeindex

default: all

# ---------------------------------------------------------------------
# Remove all trace of previous LaTeX jobs
# ---------------------------------------------------------------------
clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind entries.tex

tex: ids
	@echo "TeX files made"

ids:
	@echo "\chapter{ML Functions in the arith Library}">entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	${DOCTOTEXEXE} ${Help}/entries entries.tex

index:
	${MAKEINDEX} arith.idx

arith:
	latex arith.tex

ps:
	dvips arith.dvi -o

pdf:
	pdflatex arith.tex

all:
	make clean; make tex; make arith; make index; make arith ps pdf
