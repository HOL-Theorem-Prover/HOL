# =====================================================================
# Makefile for the hol TUTORIAL
# =====================================================================

CHAPTERS = preface.tex intro.tex ml.tex euclid.tex proof.tex theories.tex \
           title.tex combin.tex more-examples.tex

default:
	@echo "INSTRUCTIONS: Type \"make all\" to make the tutorial"

clean:
	rm -f *.dvi *.aux *.toc *.log tutorial.ps tutorial.pdf

tutorial.dvi: tutorial.tex $(CHAPTERS)
	(cd ../Logo ; make)  # makes the lantern logo
	latex tutorial.tex ; latex tutorial.tex

tutorial.ps:     tutorial.dvi
	dvips -Ppdf -G0 -f tutorial.dvi > tutorial.ps

tutorial.pdf: tutorial.ps
	ps2pdf tutorial.ps

all: tutorial.ps tutorial.pdf


