.PHONY: all clean

TARGETS = developers.pdf developers.html

all: $(TARGETS)

developers.pdf: developers.md
	pandoc --template=hol4 $< -o $@

developers.html: developers.md
	pandoc -s $< -o $@

clean:
	-/bin/rm -f $(TARGETS) developers.tex
