# =====================================================================
# Makefile for the n-bit word library documentation
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the n-bit word help files
# ---------------------------------------------------------------------
HOLDIR=../../../
Help=../help

# ---------------------------------------------------------------------
# Pathname to the doc-to-tex script and doc-to-tex.sed file
# ---------------------------------------------------------------------
DOCTOTEX=$(HOLDIR)/help/src/Doc2Tex.exe
DOCTOTEXTHM=$(HOLDIR)/Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=$(HOLDIR)/Manual/Reference/bin/doc-to-tex.sed

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

cleanAll:
	make clean; rm -f *.ps *.pdf

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
	@echo "\section{The Theory \texttt{bits}}">>theorems.tex
	/bin/sh ${DOCTOTEXTHM} ${DOCTOTEXSED} ${Help}/thms/bits theorems.tex
	@echo "\section{The Theory \texttt{numeral\\_bits}}">>theorems.tex
	/bin/sh ${DOCTOTEXTHM} ${DOCTOTEXSED} ${Help}/thms/numeral_bits theorems.tex
	@echo "\section{The Theory \texttt{word<n>}}">>theorems.tex
	/bin/sh wordn-doc wordn-doc.sed ${Help}/thms/wordn
	/bin/sh ${DOCTOTEXTHM} ${DOCTOTEXSED} ${Help}/thms/wordn theorems.tex

index:
	${MAKEINDEX} word.idx

word:
	latex word.tex

warnps:
	@if test -e word.ps; then \
            echo "** WARNING ************************************"; \
            echo "*** The file \"word.ps\" might be out of date ***"; \
            echo "***********************************************"; fi

warnpdf:
	@if test -e word.pdf; then \
            echo "** WARNING *************************************"; \
            echo "*** The file \"word.pdf\" might be out of date ***"; \
            echo "************************************************"; fi

psorpdf:
	@if dvipdf word; then \
	    make warnps; echo "* Made PDF *"; \
	 elif dvips -Ppdf -G0 word; then \
	    echo "* Made PS *"; \
	    if ps2pdf word.ps; then \
	       echo "* Made PDF *"; \
	    else \
	       make warnpdf; \
	    fi; \
	 else \
	   make warnps; make warnpdf; \
	 fi

all:
	make clean; make tex; make word; make index; make word; make psorpdf
