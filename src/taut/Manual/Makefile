# =====================================================================
# Makefile for the taut library documentation
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the taut help files
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
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind entries.tex \
		taut.{ps,pdf}

tex: ids
	@echo "TeX files made"

ids:
	@echo "\chapter{ML Functions in the taut Library}">entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	${DOCTOTEXEXE} ${Help}/entries entries.tex

index:
	${MAKEINDEX} taut.idx

taut:
	latex taut.tex

ps:
	dvips taut.dvi -o

pdf:	taut.ps
	pdflatex taut.tex

all:
	make clean; make tex; make taut; make index; make taut ps pdf
