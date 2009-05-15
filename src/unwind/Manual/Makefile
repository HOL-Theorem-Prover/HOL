# =====================================================================
# Makefile for the unwind library documentation 
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the unwind help files
# ---------------------------------------------------------------------
Help=../help

# ---------------------------------------------------------------------
# Pathname to the doc-to-tex script and doc-to-tex.sed file 
# ---------------------------------------------------------------------
DOCTOTEX=../../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../../Manual/Reference/bin/doc-to-tex.sed
DOCTOTEXEXE=../../../help/src-sml/Doc2Tex.exe

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
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg unwind.{ps,pdf}
	@echo "\begin{theindex}" > index.tex
	@echo "\mbox{}" >> index.tex
	@echo "\end{theindex}" >> index.tex

tex: ids
	@echo "TeX files made"

ids:
	@echo "\chapter{ML Functions in the unwind Library}">entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	${DOCTOTEXEXE} ${Help}/entries entries.tex

index: 
	${MAKEINDEX} unwind.idx index.tex

unwind: 
	latex unwind.tex

ps:
	dvips unwind.dvi -o

pdf:	unwind.ps
	pdflatex unwind.tex

all: 
	make clean; make tex; make unwind; make index; make unwind ps pdf
