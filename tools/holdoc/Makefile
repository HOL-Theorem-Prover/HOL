# override this by setting OCAMLPATH in your .profile; if your OCaml
# version is before 3.03a, also set OCAMLPPFLAGS to the empty string.
# define NOOCAMLPATH if you want to just use whatever is in the current path,
# either with "export NOOCAMLPATH=1; make all" or with "make NOOCAMLPATH=1 all".
OCAMLPATH?=/usr/groups/netsem/ocaml/bin
ifdef NOOCAMLPATH
OCAMLPREFIX=
else
OCAMLPREFIX=$(OCAMLPATH)/
endif
OCAMLPPFLAGS?=-pp $(OCAMLPREFIX)camlp4o
# add -pp camlp4o for ocaml version 3.03a and above, apparently


OCAMLC=$(OCAMLPREFIX)ocamlc $(OCAMLPPFLAGS)
OCAMLOPT=$(OCAMLPREFIX)ocamlopt $(OCAMLPPFLAGS)
OCAMLLEX=$(OCAMLPREFIX)ocamllex
OCAMLYACC=$(OCAMLPREFIX)ocamlyacc
OCAMLDEP=$(OCAMLPREFIX)ocamldep -native $(OCAMLPPFLAGS)

LATEX=latex
DVIPS=dvips

# files:

MLSOURCES=holdoc_init.ml holparsesupp.ml \
	mng_to_latex.ml simpledump.ml simplemosmldump.ml simplemngdump.ml \
	holdocmodel.ml holparsetools.ml mngdump.ml
MLISOURCES=holdoc_init.mli holparsesupp.mli hollex.mli simpledump.mli holparsetools.mli mngdump.mli
OTHERSOURCES=hollex.mll holparse.mly
GENMLSOURCES=hollex.ml holparse.ml
GENMLISOURCES=holparse.mli

# main target:

all: simplemngdump simplemosmldump mng_to_latex

# program targets:

simplemngdump : holdocmodel.cmx holdoc_init.cmx holparsesupp.cmx hollex.cmx holparse.cmx simpledump.cmx holparsetools.cmx simplemngdump.cmx
	$(OCAMLOPT) str.cmxa $+ -o $@

simplemosmldump : holdocmodel.cmx holdoc_init.cmx holparsesupp.cmx hollex.cmx holparse.cmx simpledump.cmx holparsetools.cmx simplemosmldump.cmx
	$(OCAMLOPT) str.cmxa $+ -o $@

mng_to_latex : holdocmodel.cmx holdoc_init.cmx holparsesupp.cmx hollex.cmx holparse.cmx simpledump.cmx holparsetools.cmx mngdump.cmx mng_to_latex.cmx
	$(OCAMLOPT) str.cmxa $+ -o $@

# other targets:

clean:
	rm -f simpledump simpletexdump simplemosmldump $(GENMLSOURCES) $(GENMLISOURCES) \
	      *.cm[iox] *.cmxa *~ '#*#' \
	      *.o \
              .depend \
              *.{aux,log} hol_to_latex mng_to_latex simplemngdump \
	      *.output

depend:	.depend

# implicit rules:

%.cmx : %.ml %.cmi
	$(OCAMLOPT) -c $<

%.cmi : %.mli
	$(OCAMLOPT) -c $<

%.tex : %.mng mng_to_latex
	./mng_to_latex < $< 2>&1 > $@ | sort | uniq -c | tee $*.errs

.PRECIOUS: %.tex

%.dvi : %.tex
	$(LATEX) $<

%.ps : %.dvi
	$(DVIPS) $< -o $@

# this one must come *after* the individual .cmx / .cmi rules:
%.cmx %.cmi : %.ml
	$(OCAMLOPT) -c $<

%.ml : %.mll
	$(OCAMLLEX) $<

%.mli %.ml : %.mly
	$(OCAMLYACC) -v $<

# extra dependencies:

# weirdly, OCaml-3.06 ocamldep can't handle .mll files!
# - and even if I include $(GENMLSOURCES) $(GENMLISOURCES), these are handled wrongly.
.depend: $(MLSOURCES) $(MLISOURCES) $(GENMLSOURCES) $(GENMLISOURCES)
	$(OCAMLDEP) $(MLSOURCES) $(MLISOURCES) $(GENMLSOURCES) $(GENMLISOURCES) > $@

-include .depend

# end

