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
IMNFILES=Store_auto.imn $(LIBDIR)/hol.imn Store.imn
  # list here the HOLDoc init (.imn) files to be used.

#
# lists of files:
#
HOLTHEORIES=$(patsubst %Script.sml,%,$(wildcard *Script.sml))
HOLTHEORYIMNS=$(addsuffix .imn, $(HOLTHEORIES))
  # this automatically computes all the theories in the current
  # directory, and their corresponding .imn files, for use
  # by lts_to_latex.

#
# Main targets:
#
all: doc

doc: StoreLTS-doc.ps

clean:
	rm -f *LTS-doc.ps *LTS.tex *LTS-doc.{tex,log,toc} *LTS.errs *.dvi TCP1_auto.imn *.aux

realclean: clean
	rm -rf *_auto.imn $(HOLTHEORYIMNS)

.PHONY: all doc clean realclean


#
# other targets:
#
Store_auto.imn: $(HOLTHEORYIMNS)
	echo '(*[ NOECHO ]*)' > $@
	cat $(filter-out Label.imn, $(HOLTHEORYIMNS)) >> $@
	cat $(filter     Label.imn, $(HOLTHEORYIMNS)) | \
		sed -e 's/CON_LIST/LIB_LIST/' - >> $@
  # one mega init file is built from the concatenation of all the
  # others, along with some filtering.


#
# hack from GNU Make manual, to set $(space) to a single space:
#
nullstring :=
space := $(nullstring) # end of the line


#
# implicit rules:
#
# route is:
# %LTSScript.sml     (original HOL script)
#   -> %LTS.tex      (rendered into LaTeX)
#   -> %LTS-doc.tex  (header and trailer attached)
#   -> %LTS-doc.dvi  (typeset)
#   -> %LTS-doc.ps   (rendered into PostScript)
# OR:
# %.mng       (original LaTeX document with embedded HOL)
#   -> %.tex  (rendered into pure LaTeX)
#   -> %.dvi  (typeset)
#   -> %.ps   (rendered into PostScript)
#
%LTS.tex : %LTSScript.sml $(if $(FAST),,$(IMNFILES) $(LTSTOLATEX))
	cat $(IMNFILES) $< | $(LTSTOLATEX) 2>&1 > $@ \
		| sort | uniq -c | tee $*LTS.errs 1>&2

%LTS-doc.tex : %LTS.tex doc-pre.template doc-post.template
	echo "% auto-generated file; do not edit" | \
        cat - doc-pre.template $< doc-post.template > $@

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
.PRECIOUS: %LTS.tex %LTS-doc.tex %.tex %.dvi


#
# extra dependencies:
#
StoreLTS-doc.dvi : $(LIBDIR)/holdoc.sty ltsmunge.sty

#
# end of Makefile
#
