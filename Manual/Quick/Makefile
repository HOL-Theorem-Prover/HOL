# =====================================================================
# Makefile for the hol Quick Reference
# =====================================================================

default:
	@echo "INSTRUCTIONS: Type \"make all\" to make Quick Reference"

clean:
	rm -f *.aux *.log *.out quick.pdf

cleanPS: clean
	rm -f *.dvi *.ps

cleanAll: cleanPS
	rm underscore.sty

underscore.sty:
	wget http://www.tex.ac.uk/tex-archive/macros/latex/contrib/misc/underscore.sty

quick.ps: quick.tex underscore.sty
	latex quick.tex; dvips -Ppdf -G0 -t landscape quick -o

quick.pdf: quick.tex underscore.sty
	pdflatex quick.tex

all: quick.pdf
