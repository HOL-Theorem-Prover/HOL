# =====================================================================
# Makefile for the quotients paper
# =====================================================================

SOURCE = quotient2.tex

default: all

clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg *.ind quotient2.{ps,pdf}

quotient2.dvi: quotient2.tex $(SOURCE)
	latex quotient2.tex
	latex quotient2.tex

quotient2.ps: quotient2.dvi
	dvips -Ppdf -G0 -f quotient2.dvi > quotient2.ps.tmp
	mv quotient2.ps.tmp $@

quotient2.pdf: quotient2.ps
	ps2pdf quotient2.ps

all: quotient2.ps quotient2.pdf
