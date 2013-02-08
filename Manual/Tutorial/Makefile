# =====================================================================
# Makefile for the hol TUTORIAL
# =====================================================================

PDFLATEX=pdflatex
DVILATEX=latex

CHAPTERS = title.tex teaser-title.tex preface.tex prologue.tex intro.tex ml.tex logic.tex \
           appetizers.tex logic-holw.tex euclid.tex parity.tex combin.tex proof-tools.tex \
           simple-cat.tex adt.tex package.tex more-examples.tex teaser-epilogue.tex \
           references.tex
OTHERS = ../LaTeX/commands.tex ../LaTeX/layout.sty ../LaTeX/ack.tex \
         ../LaTeX/proof.sty

default: pdf
all: ps pdf
ps: tutorial.ps teaser.ps
pdf: tutorial.pdf teaser.pdf

clean:
	rm -f *.dvi *.aux *.toc *.log tutorial.{ps,pdf} teaser.{ps,pdf}

tutorial.pdf: tutorial.tex $(CHAPTERS) $(OTHER)
	${PDFLATEX} tutorial.tex ; ${PDFLATEX} tutorial.tex

tutorial.dvi: tutorial.tex $(CHAPTERS) $(OTHER)
	${DVILATEX} tutorial.tex ; ${DVILATEX} tutorial.tex

tutorial.ps: tutorial.dvi
	dvips -Ppdf -G0 -f tutorial.dvi > tutorial.ps.tmp
	mv tutorial.ps.tmp $@

teaser.pdf: teaser.tex $(CHAPTERS) $(OTHER)
	${PDFLATEX} teaser.tex ; ${PDFLATEX} teaser.tex

teaser.dvi: teaser.tex $(CHAPTERS) $(OTHER)
	${DVILATEX} teaser.tex ; ${DVILATEX} teaser.tex

teaser.ps: teaser.dvi
	dvips -Ppdf -G0 -f teaser.dvi > teaser.ps.tmp
	mv teaser.ps.tmp $@
