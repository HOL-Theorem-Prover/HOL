all: hol-mode.ps hol-mode.pdf hol-mode.dvi

clean:
	/bin/rm -f hol-mode.dvi hol-mode.ps hol-mode.pdf hol-mode.aux hol-mode.log

hol-mode.ps: hol-mode.dvi
	dvips $< -o

hol-mode.pdf: hol-mode.tex
	pdflatex $<

hol-mode.dvi: hol-mode.tex
	latex $<
