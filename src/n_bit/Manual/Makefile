# =====================================================================
# Makefile for the n-bit word library documentation
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the n-bit word help files
# ---------------------------------------------------------------------
Help=../help

# ---------------------------------------------------------------------
# Pathname to the doc-to-tex script and doc-to-tex.sed file
# ---------------------------------------------------------------------
DOCTOTEX=../../../help/src/Doc2Tex.exe
DOCTOTEXTHM=../../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../../Manual/Reference/bin/doc-to-tex.sed

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
              entries.tex theorems.tex

tex: ids theorems
	@echo "TeX files made"

ids:
	@echo -n "\chapter{ML Functions in the " >entries.tex
	@echo -ne '\044' >>entries.tex
	@echo -n "n" >>entries.tex
	@echo -ne '\044' >>entries.tex
	@echo "-bit word Library}">>entries.tex
	@echo "\input{entries-intro}\label{ml-functions}" >> entries.tex
	${DOCTOTEX} ${Help}/entries entries.tex

theorems:
	@echo "\chapter{Pre-proved Theorems}" > theorems.tex
	@echo "\input{theorems-intro}" >> theorems.tex
	@echo "\section{Definitions}\label{defs}">>theorems.tex
	/bin/sh ${DOCTOTEXTHM} ${DOCTOTEXSED} ${Help}/defs theorems.tex
	@echo "\section{Theorems}">>theorems.tex
	/bin/sh ${DOCTOTEXTHM} ${DOCTOTEXSED} ${Help}/thms theorems.tex

index:
	${MAKEINDEX} word.idx

word:
	latex word.tex

all:
	make clean; make tex; make word; make index; make word;
