# =====================================================================
# Makefile for the hol TUTORIAL
# =====================================================================

default:
	@echo "INSTRUCTIONS: Type \"make all\" to make the tutorial"

clean:
	rm -f *.dvi *.aux *.toc *.log

tutorial:
	latex tutorial.tex

ps:     tutorial
	dvips -f tutorial.dvi > tutorial.ps

pdf:
	pdflatex tutorial.tex

all:
	make clean; make tutorial; make tutorial ; make pdf ps


