###############################################################################
# Makefile for the Sugar2 HOL example
###############################################################################

.PHONY: all clean world

all:
	cd regexp ; Holmake
	cd official-semantics ; Holmake
	cd executable-semantics ; Holmake -I ../regexp -I ../official-semantics

clean:
	cd regexp ; Holmake cleanAll
	cd official-semantics ; Holmake cleanAll
	cd executable-semantics ; Holmake cleanAll

world: clean all
