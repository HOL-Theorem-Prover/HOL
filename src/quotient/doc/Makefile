# =====================================================================
# Makefile for the quotients paper
# =====================================================================

default: all

clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind quotient2.{ps,pdf}

quotient2.dvi: quotient2.tex
	latex quotient2.tex
	latex quotient2.tex

quotient2.ps: quotient2.dvi
#	dvips -Ppdf -f quotient2.dvi > quotient2.ps.tmp
	dvips quotient2.dvi -o

quotient2.pdf: quotient2.tex
#	ps2pdf quotient2.ps
	pdflatex quotient2.tex

all: quotient2.ps quotient2.pdf
