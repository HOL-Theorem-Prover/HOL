.PHONY: all clean

TARGETS = developers.pdf developers.html

all: $(TARGETS)

developers.pdf: developers.tex
	latexmk -pdf developers

developers.tex: developers.md
	pandoc -s --template=hol4 $< -o $@

developers.html: developers.md
	pandoc -s $< -o $@

clean:
	-/bin/rm -f $(TARGETS) developers.tex
