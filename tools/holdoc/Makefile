OCAMLPATH=/homes/pes20/bin

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLLEX=$(OCAMLPATH)/ocamllex
OCAMLDEP=$(OCAMLPATH)/ocamldep

DVIPS=dvips

# main target:

all: simpledump lts_to_latex hostlts.ps

# program targets:

SIMPLEDUMP_OBJS=hollex.cmo simpledump.cmo

simpledump : $(SIMPLEDUMP_OBJS)
	$(OCAMLC) $(SIMPLEDUMP_OBJS) -o simpledump

LTS_TO_LATEX_OBJS=hollex.cmo holdoc_munge.cmo lts_to_latex.cmo

lts_to_latex : $(LTS_TO_LATEX_OBJS)
	$(OCAMLC) str.cma $(LTS_TO_LATEX_OBJS) -o lts_to_latex

# document targets:

Net_hostLTSScript.tex : ../HOL-model/Net_hostLTSScript.sml lts_to_latex
	./lts_to_latex < $< > $@

hostlts.dvi : hostlts.tex Net_hostLTSScript.tex ltsmunge.sty
	latex hostlts.tex

# other targets:

clean:
	rm -f simpledump lts_to_latex hollex.ml *.cm[iox] *~ '#*#' \
              .depend Net_hostLTSScript.tex hostlts.{dvi,ps}

depend:
	.depend

# implicit rules:

%.cmo : %.ml %.cmi
	$(OCAMLC) -c $<

%.cmi : %.mli
	$(OCAMLC) -c $<

%.ps : %.dvi
	$(DVIPS) $< -o $@

# this one must come *after* the individual .cmo / .cmi rules:
%.cmo %.cmi : %.ml
	$(OCAMLC) -c $<

%.ml : %.mll
	$(OCAMLLEX) $<

# extra dependencies:

.depend:
	$(OCAMLDEP) *.mli *.ml *.mll > $@

-include .depend

# end
