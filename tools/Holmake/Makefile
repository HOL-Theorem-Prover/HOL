# Unix makefile for holdep

MOSMLDIR=/local/scratch/kxs/144
MOSMLLEX=${MOSMLDIR}/bin/mosmllex
MOSMLYACC=${MOSMLDIR}/bin/mosmlyac
MOSMLC=${MOSMLDIR}/bin/mosmlc

# Unix
REMOVE=rm -f
MOVE=mv
EXEFILE=

# DOS
#REMOVE=del
#MOVE=move
#EXEFILE=.exe


#all: holdep
#holdep: Parser.uo Holdep.uo          ; $(MOSMLC) -o holdep Holdep.uo

all: Holdep.uo Parser.uo Holmake.uo       ; $(MOSMLC) -o Holmake Holmake.uo

Holmake.uo: Holmake.sml                   ; $(MOSMLC) -c Holmake.sml
Holdep.uo : Parser.ui Lexer.uo Holdep.sml ; $(MOSMLC) -c Holdep.sml
Lexer.uo  : Parser.ui Lexer.sml           ; $(MOSMLC) -c Lexer.sml
Parser.uo : Parser.sml Parser.ui          ; $(MOSMLC) -c Parser.sml
Parser.ui : Parser.sig                    ; $(MOSMLC) -c Parser.sig

Parser.sml Parser.sig : Parser.grm        ; $(MOSMLYACC) Parser.grm
Lexer.sml             : Lexer.lex         ; $(MOSMLLEX) Lexer.lex

clean:
	${REMOVE} *.u? holdep Holmake {Lexer,Parser}.{sml,sig}

