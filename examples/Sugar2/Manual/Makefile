
# =====================================================================
# Makefile for the Category B submission on Sugar 2 semantics in HOL
# to TPHOLs2002
# =====================================================================


default:
	@echo "Type \"make all\" to make CatBPaper.ps and CatBPaper.pdf"

clean:
	rm -f *.dvi *.aux *.toc *.log *.bbl *.blg CatBPaper.ps CatBPaper.pdf

CatBPaper.dvi: CatBPaper.tex
	latex CatBPaper.tex ; bibtex CatBPaper ; latex CatBPaper.tex; latex CatBPaper.tex

CatBPaper.ps: CatBPaper.dvi
	dvips -f CatBPaper.dvi > CatBPaper.ps

CatBPaper.pdf: CatBPaper.ps
	ps2pdf CatBPaper.ps

all: CatBPaper.dvi CatBPaper.ps CatBPaper.pdf

