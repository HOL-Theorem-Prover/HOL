OCAMLPATH=/home/pes20/bin

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLLEX=$(OCAMLPATH)/ocamllex
OCAMLDEP=$(OCAMLPATH)/ocamldep

# main target:

all: simpledump

# program targets:

SIMPLEDUMP_OBJS=hollex.cmo simpledump.cmo

simpledump : $(SIMPLEDUMP_OBJS)
	$(OCAMLC) $(SIMPLEDUMP_OBJS) -o simpledump

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
