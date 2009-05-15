# =====================================================================
# Makefile for the res_quan library documentation
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the help files
# ---------------------------------------------------------------------
Help=../help
LATEX=latex
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
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind \
          entries.tex theorems.tex res_quan.{ps,pdf}

tex: theorems functions
	@echo "TeX files made"

functions:
	@echo "\chapter{ML Functions in the {\tt res\_quan} Library}">entries.tex
	@echo "\label{entries}">>entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	${DOCTOTEXEXE} ${Help}/entries entries.tex

theorems:
	@echo "\chapter{Pre-proved Theorems}" > theorems.tex
	@echo "\input{theorems-intro}" >> theorems.tex
	@echo "\vskip 2mm" >> theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms theorems.tex

index:
	${MAKEINDEX} res_quan.idx

res_quan:
	$(LATEX) res_quan.tex
	$(LATEX) summary.tex

ps:
	dvips res_quan.dvi -o

pdf:	res_quan.ps
	pdflatex res_quan.tex

all:
	make clean; make tex; make res_quan; make index; make res_quan ps pdf

