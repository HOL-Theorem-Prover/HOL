OCAMLPATH=/home/pes20/bin

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLLEX=$(OCAMLPATH)/ocamllex
OCAMLDEP=$(OCAMLPATH)/ocamldep

# main target:

all: simpledump lts_to_latex

# program targets:

SIMPLEDUMP_OBJS=hollex.cmo simpledump.cmo

simpledump : $(SIMPLEDUMP_OBJS)
	$(OCAMLC) $(SIMPLEDUMP_OBJS) -o simpledump

LTS_TO_LATEX_OBJS=hollex.cmo lts_to_latex.cmo

lts_to_latex : $(LTS_TO_LATEX_OBJS)
	$(OCAMLC) $(LTS_TO_LATEX_OBJS) -o lts_to_latex

# other targets:

clean:
	rm -f simpledump hollex.ml *.cm[iox] *~ '#*#' .depend

depend:
	$(OCAMLDEP) *.mli *.mll *.ml > .depend


# implicit rules:

%.cmo : %.ml %.cmi
	$(OCAMLC) -c $<

%.cmi : %.mli
	$(OCAMLC) -c $<

# this one must come *after* the individual .cmo / .cmi rules:
%.cmo %.cmi : %.ml
	$(OCAMLC) -c $<

%.ml : %.mll
	$(OCAMLLEX) $<

# extra dependencies:

-include .depend

# end
