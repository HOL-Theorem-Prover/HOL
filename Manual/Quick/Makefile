# =====================================================================
# Makefile for the hol Quick Reference
# =====================================================================

default:  quick.pdf
all: quick.ps quick.pdf

clean:
	rm -f *.aux *.log *.out quick.{ps,pdf}

quick.ps: quick.tex
	latex quick.tex; dvips -Ppdf -G0 -t landscape quick -o

quick.pdf: quick.tex
	pdflatex quick.tex
