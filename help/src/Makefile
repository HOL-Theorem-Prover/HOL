# Makefile for help utility recompilation
#include ../../Makefile.inc

MOSMLHOME=/home/kxs/200
MOSMLBIN=$(MOSMLHOME)/bin
MOSMLTOOLS=$(MOSMLBIN)/camlrunm $(MOSMLHOME)/tools
MOSMLC=$(MOSMLBIN)/mosmlc -c 
MOSMLL=$(MOSMLBIN)/mosmlc
MOSMLLEX=$(MOSMLBIN)/mosmllex
MOSMLYACC=$(MOSMLBIN)/mosmlyac

.SUFFIXES :
.SUFFIXES : .sml .sig .ui .uo .mlp .lex .c .o

.sig.ui:
	$(MOSMLC) $(COMPFLAGS) $<

.sml.uo:
	$(MOSMLC) $(COMPFLAGS) $<

.lex.sml:
	$(MOSMLLEX) $<

all: Asynt.uo Database.uo Hasht.uo Htmlsigs.uo Lexer.uo Parser.uo Parsspec.uo \
	Printbase.uo Stack.uo Texsigs.uo makebase.uo makebase

Parser.sml Parser.sig: Parser.grm
	$(MOSMLYACC) Parser.grm

Lexer.sml Lexer.sig: Lexer.lex
	$(MOSMLLEX) Lexer.lex

makebase : Database.uo Htmlsigs.uo Lexer.uo Parser.uo Parsspec.uo \
    Printbase.uo Texsigs.uo makebase.uo
	$(MOSMLL) -o makebase makebase.uo

install:
	cp helpsigs.val $(LIBDIR)
	test -d $(DOCDIR)/mosmllib || mkdir -p $(DOCDIR)/mosmllib
	cp htmlsigs/*.html $(DOCDIR)/mosmllib
	cp index.html $(DOCDIR)/mosmllib

depend: Lexer.sml Parser.sml 
	rm -f Makefile.bak
	mv Makefile Makefile.bak
	$(MOSMLTOOLS)/cutdeps < Makefile.bak > Makefile
	$(MOSMLTOOLS)/mosmldep >> Makefile

clean:
	rm -f Parser.sig Parser.sml Lexer.sml
	rm -f makebase index.txt index.tex texsigsigs.tex
	rm -f *.ui
	rm -f *.uo
	rm -f Makefile.bak

### DO NOT DELETE THIS LINE
Hasht.uo: Hasht.ui 
Parser.ui: Asynt.uo 
Parser.uo: Parser.ui Asynt.uo 
makebase.uo: Keepers.uo Htmlsigs.ui Database.ui Printbase.uo Parsspec.uo 
Texsigs.uo: Texsigs.ui Database.ui 
Stack.uo: Stack.ui 
Printbase.uo: Database.ui 
Parsspec.uo: Asynt.uo Parser.ui Lexer.uo Database.ui 
Htmlsigs.uo: Htmlsigs.ui Database.ui 
Lexer.uo: Parser.ui Stack.ui Hasht.ui 
Database.uo: Database.ui 
