# =====================================================================
# Makefile for the HOL DESCRIPTION
# =====================================================================

PDFLATEX=pdflatex
DVILATEX=latex
MAKEINDEX=makeindex
BIBTEX=bibtex

CHAPTERS = conv.tex drules.tex HolQbf.tex HolSat.tex HolSmt.tex		\
           libraries.tex misc.tex preface.tex semantics.tex syntax.tex	\
           tactics.tex theories.tex title.tex system.tex definitions.tex
OTHER = ../LaTeX/commands.tex ../LaTeX/layout.sty ../LaTeX/ack.tex

default: pdf
pdf: description.pdf HolBdd.pdf holCheck.pdf

clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind description.pdf \
            *.bbl *.blg HolBdd.pdf holCheck.pdf

description.pdf: description.tex $(CHAPTERS) $(OTHER)
	${PDFLATEX}  description
	${MAKEINDEX} description
	${BIBTEX}    description
	${PDFLATEX}  description
	${PDFLATEX}  description

HolBdd.pdf: HolBdd.tex
	${PDFLATEX} HolBdd
	${BIBTEX}   HolBdd
	${PDFLATEX} HolBdd
	${PDFLATEX} HolBdd

holCheck.pdf: holCheck.tex
	${PDFLATEX} holCheck
	${PDFLATEX} holCheck

description.dvi: description.tex $(CHAPTERS) $(OTHER)
	${DVILATEX}  description
	${MAKEINDEX} description
	${BIBTEX}    description
	${DVILATEX}  description
	${DVILATEX}  description

description.ps: description.dvi
	dvips -Ppdf -G0 -f description.dvi > description.ps.tmp
	mv description.ps.tmp $@

HolBdd.ps:  HolBdd.tex
	${DVILATEX} HolBdd
	${BIBTEX}   HolBdd
	${DVILATEX} HolBdd
	${DVILATEX} HolBdd
	dvips -Ppdf -G0 -f HolBdd.dvi > HolBdd.ps.tmp
	mv HolBdd.ps.tmp $@

holCheck.ps: holCheck.tex
	${DVILATEX} holCheck
	${DVILATEX} holCheck
	dvips -Ppdf -G0 -f holCheck.dvi > holCheck.ps.tmp
	mv holCheck.ps.tmp $@
