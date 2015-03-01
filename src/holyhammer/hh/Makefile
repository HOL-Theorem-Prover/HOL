ALLFILES=$(HH1) $(FILES)
# HOL Light files
HL=hh1/lib hh1/fusion hh1/basics hh1/printer hh1/preterm hh1/hl_parser hh1/equal \
    hh1/bool hh1/drule hh1/tactics hh1/simp hh1/theorems hh1/canon hh1/fol hh1/follist hh1/meson
# HH1 (old files)
HH1=hh1/hh_symbols hh1/features_dt hh1/hh_tac hh1/hh_write
# HH2 (new files)
FILES=hh_parse hh_lexer read predict init dependency thf1hh1 predict_knn 
ALLFILES=$(HL) $(HH1) $(FILES)

FILES_CMO=$(addsuffix .cmo,$(ALLFILES))
FILES_CMX=$(addsuffix .cmx,$(ALLFILES))

all: hh_h4

hh_h4: main_h4.ml $(FILES_CMX) Makefile
	ocamlopt nums.cmxa str.cmxa unix.cmxa -o $@ -I hh1 $(FILES_CMX) $<

%.ml: %.mly
	ocamlyacc $< # -v
	rm $(<:y=i)

%_lexer.ml: %_lexer.mll %_parse.ml
	ocamllex $<

%.cmx: %.ml
	ocamlopt -c -I hh1 $<

%.cmo: %.ml
	ocamlc -c -I hh1 $<

clean:
	rm -f hh_h4 *cmx *cmo *cmi *_lexer.ml *_parse.ml *.o

.depend: $(addsuffix .ml,$(FILES))
	ocamldep $^ main.ml > $@

include .depend
