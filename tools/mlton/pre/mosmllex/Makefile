###############################################################################
#  Makefile for a standard ML version of mosmllex
###############################################################################

.PHONY: all build test clean world

SML = smlnj
PREFIX = lexgen
IMAGE = $(PREFIX).x86-linux
OBJ = $(IMAGE) test/Scanner.sml

all: build test

build: $(IMAGE)

$(IMAGE):
	echo 'SMLofNJ.exportFn("$(PREFIX)",LexGen.main);' | $(SML) -m sources.cm

test: test/Scanner.sml

test/Scanner.sml: $(IMAGE)
	cd test ; $(SML) @SMLload=../$(IMAGE) Scanner.lex

clean:
	rm -f $(OBJ)
	rm -rf CM lib/CM

world: clean all
