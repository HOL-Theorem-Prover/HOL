###############################################################################
#  Makefile interface to Holmake
#  Created by Joe Hurd, June 2002
###############################################################################

HOL = ../../../bin/hol.bare
HOLMAKE = Holmake

.PHONY: all
all: verification-log dining-cryptographers

.PHONY: clean
clean:
	rm -f verification-log
	$(HOLMAKE) cleanAll

.PHONY: world
world: clean all

verification-log: verification.sml ../src/pgclLib.uo
	$(HOL) <verification.sml | tee verification-log

dining-cryptographers:
	$(HOLMAKE) -I ../src --qof simpledcTheory.uo
