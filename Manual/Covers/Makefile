# Makefile for HOL Manual title and end pages.  This is separate from the main
# manual stuff because of the heavy PostScript hacking involved.

# The following variables are needed:
#
#   LATEX -- The name of the LaTeX command normally used at this site.
#   DVI2PS -- The name of the dvi -> ps converter.
#   DVI2PSOPTS -- Options for the converter named in DVI2PS.

LATEX = latex
DVI2PS = dvips
DVI2PSOPTS =
RM = rm -f

TITLE_PSFILES = CRC.ps DESCRIPTION.ps REFERENCE.ps TUTORIAL.ps \
                LIBRARIES.ps arms.ps dsto.ps
END_PSFILES = LANTERN.ps


all: endpages.ps titlepages.ps

endpages.dvi: $(END_PSFILES) endpages.tex endpages.sty
	$(LATEX) endpages
	@echo "===> endpages.dvi created"

titlepages.dvi: $(TITLE_PSFILES) titlepages.tex titlepages.sty
	$(LATEX) titlepages
	@echo "===> titlepages.dvi created"

dvi: endpages.dvi titlepages.dvi

endpages.ps: endpages.dvi
	$(DVI2PS) $(DVI2PSOPTS) endpages.dvi

titlepages.ps: titlepages.dvi
	$(DVI2PS) $(DVI2PSOPTS) titlepages.dvi

clean:
	$(RM) *.log core *.aux *~ LOG *.dvi endpages.ps titlepages.ps


