# Model Makefile for munging.  Requires GNU make.

#
# locations of various programs:
#
HOLDOCDIR=../..
LIBDIR=../common

LTSTOLATEX=$(HOLDOCDIR)/lts_to_latex
MNGTOLATEX=$(HOLDOCDIR)/mng_to_latex
LATEX=latex
DVIPS=dvips

#
# location of holdoc.sty and other TeX style files:
#
EXTRATEXINPUTS=$(LIBDIR)

#
# list of .imn include files to use:
#
IMNFILES=$(LIBDIR)/hol.imn examples.imn
  # list here the HOLDoc init (.imn) files to be used.

#
# Main targets:
#
all: example1.ps

clean:
	rm -f example1.tex example1.ps *.{log,toc,dvi,aux} *.errs

.PHONY: all clean


#
# hack from GNU Make manual, to set $(space) to a single space:
#
nullstring :=
space := $(nullstring) # end of the line

#
# implicit rules:
#
# route is:
# %.mng       (original LaTeX document with embedded HOL)
#   -> %.tex  (rendered into pure LaTeX)
#   -> %.dvi  (typeset)
#   -> %.ps   (rendered into PostScript)
#
%.tex : %.mng $(IMNFILES)
	  cat $(IMNFILES) $*.mng \
		  | $(MNGTOLATEX) 2>&1 > $*.tex \
		  | sort | uniq -c | tee $*.errs

%.dvi : %.tex
	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(LATEX) $<

%.ps : %.dvi
	$(DVIPS) $< -o $@.tmp
	mv $@.tmp $@

# keep these around for debugging purposes:
.PRECIOUS: %.tex %.dvi


#
# extra dependencies:
#
example1.dvi : $(LIBDIR)/holdoc.sty examples.sty

#
# end of Makefile
#
