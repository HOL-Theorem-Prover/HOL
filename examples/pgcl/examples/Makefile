###############################################################################
#  Makefile interface to Holmake
#  Created by Joe Hurd, June 2002
###############################################################################

HOL = hol.bare.unquote

verification-log: verification.sml ../src/pgclLib.uo
	$(HOL) <verification.sml | tee verification-log

all: verification-log

clean:
	rm -f verification-log
