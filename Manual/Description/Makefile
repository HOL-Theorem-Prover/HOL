# =====================================================================
# Makefile for the hol DESCRIPTION
# =====================================================================

# ---------------------------------------------------------------------
# Pathnames: MAKEINDEX = makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=makeindex
CHAPTERS = conv.tex drules.tex libraries.tex logic.tex misc.tex \
           preface.tex references.tex semantics.tex syntax.tex \
           tactics.tex theories.tex title.tex system.tex

default: all

clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind description.{ps,pdf}

description.dvi: description.tex $(CHAPTERS) ../LaTeX/commands.tex
#	(cd ../Logo ; make)  # makes the lantern logo
	latex description.tex
	${MAKEINDEX} description.idx
	latex description.tex

description.ps: description.dvi
	dvips -Ppdf -G0 -f description.dvi > description.ps

description.pdf: description.ps
	ps2pdf description.ps

all: description.ps description.pdf
