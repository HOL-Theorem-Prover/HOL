# Makefile for help utility recompilation
#
# This makefile should only be run by developers.  It is not intended for
# distribution.

MOSMLHOME=/local/scratch/kxs/144
MOSMLC=${MOSMLHOME}/bin/mosmlc
COMPFLAGS=-I ${MOSMLHOME}/src/compiler
MOSMLLEX=${MOSMLHOME}/bin/mosmllex
MOSMLYACC=${MOSMLHOME}/bin/mosmlyac

DOCDIRFILE = ../../tools/documentation-directories

index: ./mk_dbs adoc-files
	./mk_dbs ../../ && touch index

adoc-files: $(DOCDIRFILE)
	./gen-adocs.sh $(DOCDIRFILE) && touch adoc-files



mk_dbs: mk_dbs.uo Database.uo Lexer.uo Parser.uo Parsspec.uo
	$(MOSMLC) $(COMPFLAGS) -o $@ mk_dbs.uo

Parser.sml Parser.sig: Parser.grm
	$(MOSMLYACC) Parser.grm

.SUFFIXES :
.SUFFIXES : .sml .sig .ui .uo .mlp .lex .c .o

.sig.ui:
	$(MOSMLC) -c $(COMPFLAGS) $<

.sml.uo:
	$(MOSMLC) -c $(COMPFLAGS) $<

.lex.sml:
	$(MOSMLLEX) $<

clean:
	rm -f Parser.sig Parser.sml Lexer.sml mk_dbs index adoc-files
	rm -f *.ui
	rm -f *.uo
	./clean-adocs.sh docdirs

### DO NOT DELETE THIS LINE
Parser.uo: Parser.ui
Lexer.uo: Parser.ui
Database.uo: Database.ui
Parsspec.uo: Parser.ui Lexer.uo Database.ui
mk_dbs.uo: Database.ui Parsspec.uo
