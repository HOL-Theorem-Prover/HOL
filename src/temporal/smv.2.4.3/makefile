CC = gcc
CFLAGS = -I. -O4

OBJ = grammar.o input.o main.o assoc.o bdd.o  hash.o node.o storage.o \
	string.o symbols.o
LIB = -lm 


EXEC = smv

$(EXEC): $(OBJ) $(DEBUG)
	rm -f $(EXEC)
	$(CC) $(CFLAGS) $(OBJ) $(LIB) $(DEBUG) -o $(EXEC)
grammar.c grammar.tab.h: grammar.y
	bison -d grammar.y; mv grammar.tab.c grammar.c
input.c: input.lex
	flex input.lex; mv lex.yy.c input.c

main.o: main.c grammar.tab.h assoc.h  storage.h bdd.h hash.h node.h string.h
assoc.o: assoc.c assoc.h storage.h hash.h node.h
bdd.o: bdd.c assoc.h storage.h bdd.h hash.h node.h
symbols.o : symbols.c storage.h node.h hash.h bdd.h assoc.h grammar.tab.h
hash.o: hash.c storage.h hash.h
node.o: node.c grammar.tab.h assoc.h storage.h bdd.h hash.h node.h
storage.o: storage.c storage.h
string.o: string.c assoc.h storage.h hash.h string.h
grammar.o: grammar.c storage.h node.h hash.h assoc.h
input.o: input.c node.h grammar.tab.h


clean:
	rm -f *.o grammar.c input.c grammar.tab.h