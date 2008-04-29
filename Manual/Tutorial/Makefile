# =====================================================================
# Makefile for the hol TUTORIAL
# =====================================================================

PDFLATEX=pdflatex
DVILATEX=latex

CHAPTERS = title.tex preface.tex intro.tex ml.tex logic.tex euclid.tex \
           parity.tex combin.tex proof-tools.tex more-examples.tex references.tex
OTHERS = ../LaTeX/commands.tex ../LaTeX/layout.sty ../LaTeX/ack.tex \
         ../LaTeX/proof.sty

default: pdf
all: ps pdf
ps: tutorial.ps
pdf: tutorial.pdf

clean:
	rm -f *.dvi *.aux *.toc *.log tutorial.{ps,pdf}

tutorial.pdf: tutorial.tex $(CHAPTERS) $(OTHER)
	${PDFLATEX} tutorial.tex ; ${PDFLATEX} tutorial.tex

tutorial.dvi: tutorial.tex $(CHAPTERS) $(OTHER)
	${DVILATEX} tutorial.tex ; ${DVILATEX} tutorial.tex

tutorial.ps: tutorial.dvi
	dvips -Ppdf -G0 -f tutorial.dvi > tutorial.ps.tmp
	mv tutorial.ps.tmp $@
