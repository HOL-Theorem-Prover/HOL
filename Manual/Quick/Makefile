# =====================================================================
# Makefile for the hol Quick Reference
# =====================================================================

default:
	@echo "INSTRUCTIONS: Type \"make all\" to make Quick Reference"

clean:
	rm -f *.aux *.log *.out quick.pdf

cleanPS: clean
	rm -f *.dvi *.ps

underscore.sty:
	@echo "**********************************************"
	@echo "*** Please download underscore.sty from CTAN *"
	@echo "**********************************************"
	@echo

quick.ps: quick.tex underscore.sty
	latex quick.tex; dvips -Ppdf -G0 -t landscape quick -o

quick.pdf: quick.tex underscore.sty
	pdflatex quick.tex

all: quick.pdf
