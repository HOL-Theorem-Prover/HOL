# Unix makefile for Holmake

# This makefile does NOT build Holmake when hol is installed.  Rather, it is
# just a convenience for developers.  In particular, the little script
# fake_src.pl is not what does the substitutions in Holmake.src; developers
# must ensure that tools/configure.sml does the right thing with these
# substitutions.

MOSMLDIR=/local/scratch/kxs/200
MOSMLLEX=${MOSMLDIR}/bin/mosmllex
MOSMLYACC=${MOSMLDIR}/bin/mosmlyac
MOSMLC=${MOSMLDIR}/bin/mosmlc

# Unix
REMOVE=rm -f
MOVE=mv
EXEFILE=

all: Holmake Holdep.uo Parser.uo Holmake.uo Holmake_rules.uo

Holmake: Holmake.uo Holdep.uo Parser.uo Lexer.uo Holmake_parse.uo \
         Holmake_tokens.uo Holmake_rules.uo Holmake_types.uo
	$(MOSMLC) -o Holmake Holmake.uo

Holmake.sml: Holmake.src fake_src.pl Holdep.uo
	perl fake_src.pl < Holmake.src > Holmake.sml

Holmake.uo: Holmake.sml Holmake_rules.ui Systeml.ui
	$(MOSMLC) -c Holmake.sml
Holdep.uo : Parser.ui Lexer.uo Holdep.sml ; $(MOSMLC) -c Holdep.sml
Lexer.uo  : Parser.ui Lexer.sml           ; $(MOSMLC) -c Lexer.sml
Parser.uo : Parser.sml Parser.ui          ; $(MOSMLC) -c Parser.sml
Parser.ui : Parser.sig                    ; $(MOSMLC) -c Parser.sig
Systeml.uo Systeml.ui: Systeml.sml        ; $(MOSMLC) -c Systeml.sml

Parser.sml Parser.sig : Parser.grm        ; $(MOSMLYACC) Parser.grm
Lexer.sml             : Lexer.lex         ; $(MOSMLLEX) Lexer.lex

Holmake_parse.sig Holmake_parse.sml : Holmake_parse.grm
	$(MOSMLYACC) Holmake_parse.grm
Holmake_parse.uo: Holmake_parse.sml Holmake_parse.ui Holmake_types.ui
	$(MOSMLC) -c Holmake_parse.sml
Holmake_parse.ui: Holmake_parse.sig Holmake_types.ui
	$(MOSMLC) -c $<
Holmake_tokens.sml : Holmake_tokens.lex
	$(MOSMLLEX) Holmake_tokens.lex
Holmake_rules.ui: Holmake_rules.sig Holmake_types.ui
	$(MOSMLC) -c $<
Holmake_rules.uo: Holmake_rules.sml Holmake_rules.ui Holmake_tokens.ui \
                  Holmake_parse.ui Holmake_parse.uo Holmake_tokens.uo \
	          Holmake_types.ui
	$(MOSMLC) -c $<
Holmake_tokens.ui Holmake_tokens.uo: Holmake_tokens.sml Holmake_parse.ui
	$(MOSMLC) -c $<
Holmake_types.ui: Holmake_types.sig
	$(MOSMLC) -c $<
Holmake_types.uo: Holmake_types.sml
	$(MOSMLC) -c $<

clean:
	${REMOVE} *.u? holdep Holmake {Lexer,Parser}.{sml,sig} Holmake.sml \
                  Holmake_{parse,tokens}.{sig,sml}

