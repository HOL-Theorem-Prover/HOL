# =====================================================================
# Makefile for the hol DESCRIPTION
# =====================================================================

# ---------------------------------------------------------------------
# Pathnames: MAKEINDEX = makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=makeindex

default:
	@echo "INSTRUCTIONS: Type \"make all\" to make DESCRIPTION"

clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind

index:
	${MAKEINDEX} description.idx

description:
	latex description.tex

ps:
	dvips -f description.dvi > description.ps

pdf:
	pdflatex description.tex

all:
	make clean; make description; make index; make description; make pdf ps
