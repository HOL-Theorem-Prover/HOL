# =====================================================================
# Makefile for the word library documentation 
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the help files
# ---------------------------------------------------------------------


HOLMANDIR=/usr/groups/hol/hol90/Manual

Help=../help
LATEX=latex
# ---------------------------------------------------------------------
# Pathname to the doc-to-tex script and doc-to-tex.sed file 
# ---------------------------------------------------------------------
DOCTOTEX=$(HOLMANDIR)/Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=$(HOLMANDIR)/Manual/Reference/bin/doc-to-tex.sed

# ---------------------------------------------------------------------
# Pathname to the makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=$(HOLMANDIR)/Manual/LaTeX/makeindex $(HOLMANDIR)
#MAKEINDEX=makeindex

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

tex: theorems functions
	@echo "TeX files made"

functions:
	@echo "\chapter{ML Functions in the {\tt word} Library}">entries.tex
	@echo "\label{entries}">>entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/entries entries.tex

theorems:
	@echo "\chapter{Pre-proved Theorems}" > theorems.tex
	@echo "\input{theorems-intro}" >> theorems.tex
	@echo "\section{The theory {\tt word\_base}}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/word_base theorems.tex
	@echo "\section{The theory {\tt word\_bitop}}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/word_bitop theorems.tex
	@echo "\section{The theory {\tt word\_num}}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/word_num theorems.tex
	@echo "\section{The theory {\tt bword\_bitop}}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/bword_bitop theorems.tex
	@echo "\section{The theory {\tt bword\_num}}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/bword_num theorems.tex
	@echo "\section{The theory {\tt bword\_arith}}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/bword_arith theorems.tex

index: 
	${MAKEINDEX} word.idx index.tex

word: 
	$(LATEX) word.tex 

all: 
	make clean; make tex; make word; make index; make word

