# =====================================================================
# Makefile for the hol LOGIC
# =====================================================================

PDFLATEX=pdflatex
DVILATEX=latex
BIBTEX=bibtex

CHAPTERS = syntax.tex preface.tex semantics.tex title.tex
OTHER = ../LaTeX/commands.tex ../LaTeX/layout.sty ../LaTeX/ack.tex

default: pdf
all: ps pdf
ps: logic.ps
pdf: logic.pdf

clean:
	rm -f *.dvi *.aux *.toc *.log logic.{ps,pdf}

logic.pdf: logic.tex $(CHAPTERS) $(OTHER)
	${PDFLATEX} logic
	${BIBTEX}   logic
	${PDFLATEX} logic
	${PDFLATEX} logic

logic.dvi: logic.tex $(CHAPTERS) $(OTHER)
	${DVILATEX} logic
	${BIBTEX}   logic
	${DVILATEX} logic
	${DVILATEX} logic

logic.ps: logic.dvi
	dvips -Ppdf -G0 -f logic.dvi > logic.ps.tmp
	mv logic.ps.tmp $@
