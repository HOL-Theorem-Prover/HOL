.PHONY: all

all: developers.pdf developers.html

developers.pdf: developers.tex
	latexmk -pdf developers

developers.tex: developers.md
	pandoc -s $< -o $@

developers.html: developers.md
	pandoc -s $< -o $@
