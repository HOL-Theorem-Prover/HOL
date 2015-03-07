ALLFILES=$(HH1) $(FILES)
# HOL Light files
HL=hh1/lib hh1/fusion hh1/basics hh1/printer hh1/preterm hh1/hl_parser hh1/equal \
    hh1/bool hh1/drule hh1/tactics hh1/simp hh1/theorems hh1/canon hh1/fol hh1/follist hh1/meson
# HH1 (old files)
HH1=hh1/hh_symbols hh1/features_dt hh1/hh_tac hh1/hh_write
# HH2 (new files)
FILES=hh_parse hh_lexer fof_parse fof_lexer read predict thf0hh1 \
      init dependency thf1hh1 predict_knn proto
ALLFILES=$(HL) $(HH1) $(FILES)

FILES_CMO=$(addsuffix .cmo,$(ALLFILES))
FILES_CMX=$(addsuffix .cmx,$(ALLFILES))

all: hhall hhthf0 hh

hhthf0: mainthf0.ml $(FILES_CMX) Makefile
	ocamlopt nums.cmxa str.cmxa unix.cmxa -o $@ -I hh1 $(FILES_CMX) $<

hhall:  mainall.ml $(FILES_CMX) Makefile
	ocamlopt nums.cmxa str.cmxa unix.cmxa -o $@ -I hh1 $(FILES_CMX) $<

hh:     main.ml $(FILES_CMX) Makefile
	ocamlopt nums.cmxa str.cmxa unix.cmxa -o $@ -I hh1 $(FILES_CMX) $<

fofdt:    mainfofdt.ml $(FILES_CMX) Makefile
	ocamlopt nums.cmxa str.cmxa unix.cmxa -o $@ -I hh1 $(FILES_CMX) $<

fofmeson: mainmeson.ml $(FILES_CMX)
	ocamlopt nums.cmxa str.cmxa unix.cmxa -o $@ -I hh1 $(FILES_CMX) $<

# Run "rlwrap ./top -I hh1"
top: $(FILES_CMO) Makefile
	ocamlmktop nums.cma str.cma unix.cma -o $@ -I hh1 $(FILES_CMO)

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
	rm hhthf0 hhall hh top *cmx *cmo *cmi *_lexer.ml *_parse.ml *.o *~

.depend: $(addsuffix .ml,$(FILES))
	ocamldep $^ main.ml > $@

include .depend
