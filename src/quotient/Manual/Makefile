# =====================================================================
# Makefile for the quotients paper
# =====================================================================

default: all

clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind quotient.ps quotient.pdf

quotient.dvi: quotient.tex
	latex quotient.tex
	latex quotient.tex

quotient.ps: quotient.dvi
	dvips -t letter quotient.dvi -o

quotient.pdf: quotient.tex
#	ps2pdf quotient.ps
	pdflatex quotient.tex

all: quotient.ps quotient.pdf
