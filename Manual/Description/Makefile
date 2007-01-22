# =====================================================================
# Makefile for the hol DESCRIPTION
# =====================================================================

# ---------------------------------------------------------------------
# Pathnames: MAKEINDEX = makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=makeindex
BIBTEX=bibtex
CHAPTERS = conv.tex drules.tex libraries.tex misc.tex \
           preface.tex semantics.tex syntax.tex \
           tactics.tex theories.tex title.tex system.tex definitions.tex

default: all

clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind description.{ps,pdf} *.bbl *.blg

description.dvi: description.tex $(CHAPTERS) ../LaTeX/commands.tex
#	(cd ../Logo ; make)  # makes the lantern logo
	latex description.tex
	${MAKEINDEX} description.idx
	${BIBTEX} description
	latex description.tex
	latex description.tex

description.ps: description.dvi
	dvips -Ppdf -G0 -f description.dvi > description.ps.tmp
	mv description.ps.tmp $@

description.pdf: description.ps
	ps2pdf description.ps

all: description.ps description.pdf
