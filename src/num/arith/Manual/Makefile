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
DOCTOTEX=../../../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../../../Manual/Reference/bin/doc-to-tex.sed

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
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind

tex: ids
	@echo "TeX files made"

ids:
	@echo "\chapter{ML Functions in the arith Library}">entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/entries entries.tex

index:
	${MAKEINDEX} arith.idx

arith:
	latex arith.tex

all:
	make clean; make tex; make arith; make index; make arith
