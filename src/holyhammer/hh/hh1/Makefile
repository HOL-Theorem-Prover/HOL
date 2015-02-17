FILES=lib fusion basics printer preterm hl_parser equal bool drule tactics simp theorems canon fol follist meson hh_symbols features_dt hh_tac hh_write


FILES_CMO=$(addsuffix .cmo,$(FILES))
FILES_CMX=$(addsuffix .cmx,$(FILES))

all: $(FILES_CMO) $(FILES_CMX)

main: $(FILES_CMX) Makefile
	ocamlopt nums.cmxa str.cmxa -o $@ $(FILES_CMX)

top: $(FILES_CMO) Makefile
	ocamlmktop nums.cma str.cma -o $@ $(FILES_CMO)

%.cmx: %.ml
	ocamlopt -c $<

%.cmo: %.ml
	ocamlc -c $<

clean:
	rm main top *cmx *cmo *cmi *.o *~

.depend:
	ocamldep $(addsuffix .ml,$(FILES)) > $@

include .depend
