# =====================================================================
# Makefile for the hol DESCRIPTION
# =====================================================================

# ---------------------------------------------------------------------
# Pathnames: MAKEINDEX = makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=makeindex
BIBTEX=bibtex
CHAPTERS = syntax.tex preface.tex semantics.tex title.tex

default: all

clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind logic.{ps,pdf} *.bbl *.blg

logic.dvi: logic.tex $(CHAPTERS) ../LaTeX/commands.tex
#	(cd ../Logo ; make)  # makes the lantern logo
	latex logic.tex
	${BIBTEX} logic
	latex logic.tex
	latex logic.tex

logic.ps: logic.dvi
	dvips -Ppdf -G0 -f logic.dvi > logic.ps.tmp
	mv logic.ps.tmp $@

logic.pdf: logic.ps
	ps2pdf logic.ps

all: logic.ps logic.pdf
