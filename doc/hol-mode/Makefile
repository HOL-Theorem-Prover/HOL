all: hol-mode.ps hol-mode.dvi

clean:
	/bin/rm -f hol-mode.dvi hol-mode.ps hol-mode.aux hol-mode.log

hol-mode.ps: hol-mode.dvi
	dvips $<

hol-mode.dvi: hol-mode.tex
	latex $<