# override this by setting OCAMLPATH in your .profile; if your OCaml
# version is before 3.03a, also set OCAMLPPFLAGS to the empty string.
OCAMLPATH?=/usr/groups/netsem/ocaml/bin
OCAMLPPFLAGS?=-pp $(OCAMLPATH)/camlp4o
# add -pp camlp4o for ocaml version 3.03a and above, apparently

OCAMLC=$(OCAMLPATH)/ocamlc $(OCAMLPPFLAGS)
OCAMLLEX=$(OCAMLPATH)/ocamllex
OCAMLYACC=${OCAMLPATH}/ocamlyacc
OCAMLDEP=$(OCAMLPATH)/ocamldep $(OCAMLPPFLAGS)

LATEX=latex
DVIPS=dvips

# main target:

all: simpledump simpletexdump lts_to_latex mng_to_latex hol_to_latex

# program targets:

SIMPLEDUMP_OBJS=hollex.cmo simpledump.cmo

simpledump : $(SIMPLEDUMP_OBJS)
	$(OCAMLC) $(SIMPLEDUMP_OBJS) -o simpledump

SIMPLETEXDUMP_OBJS=hollex.cmo simpletexdump.cmo

simpletexdump : $(SIMPLETEXDUMP_OBJS)
	$(OCAMLC) $(SIMPLETEXDUMP_OBJS) -o simpletexdump

LTS_TO_LATEX_OBJS=hollex.cmo holdoc_init.cmo holdoc_munge.cmo lts_to_latex.cmo

lts_to_latex : $(LTS_TO_LATEX_OBJS)
	$(OCAMLC) str.cma $(LTS_TO_LATEX_OBJS) -o lts_to_latex

MNG_TO_LATEX_OBJS=hollex.cmo holdoc_init.cmo holdoc_munge.cmo mng_to_latex.cmo

mng_to_latex : $(MNG_TO_LATEX_OBJS)
	$(OCAMLC) str.cma $(MNG_TO_LATEX_OBJS) -o mng_to_latex

HOL_TO_LATEX_OBJS=hollex.cmo holdoc_init.cmo holdoc_munge.cmo hol_to_latex.cmo

hol_to_latex : $(HOL_TO_LATEX_OBJS)
	$(OCAMLC) str.cma $(HOL_TO_LATEX_OBJS) -o hol_to_latex

# document targets:

Net_hostLTSScript.tex : ../HOL-model/Net_hostLTSScript.sml lts_to_latex
	cat ../HOL-model/Net.imn $< | ./lts_to_latex 2>&1 > $@ \
		| sort | uniq -c | tee Net_hostLTSScript.errs

hostlts.dvi : hostlts.tex Net_hostLTSScript.tex ltsmunge.sty
	latex hostlts.tex

# other targets:

clean:
	rm -f simpledump simpletexdump lts_to_latex hollex.ml *.cm[iox] *~ '#*#' \
              .depend Net_hostLTSScript.tex hostlts.{dvi,ps} \
              *.{aux,log} hol_to_latex mng_to_latex

depend:	.depend

# implicit rules:

%.cmo : %.ml %.cmi
	$(OCAMLC) -c $<

%.cmi : %.mli
	$(OCAMLC) -c $<

%.tex : %.mng mng_to_latex
	./mng_to_latex < $< 2>&1 > $@ | sort | uniq -c | tee $*.errs

.PRECIOUS: %.tex

%.dvi : %.tex
	$(LATEX) $<

%.ps : %.dvi
	$(DVIPS) $< -o $@

# this one must come *after* the individual .cmo / .cmi rules:
%.cmo %.cmi : %.ml
	$(OCAMLC) -c $<

%.ml : %.mll
	$(OCAMLLEX) $<

# extra dependencies:

# weirdly, OCaml-3.06 ocamldep can't handle .mll files!
.depend: *.mli *.ml
	$(OCAMLDEP) *.mli *.ml > $@

-include .depend

# end
