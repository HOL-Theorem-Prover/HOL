LEX=flex
CC=gcc
#archOS=`../../tools/archOS`

#-------------------------------------------------------------------------
# pipe
#
# A shell script to allow a file to be piped through the filter without
# an explicit pipe having to appear in the command executed by the SML
# process.
#-------------------------------------------------------------------------

#pipe: $(PIPE)

#$(PIPE):
#	@-mkdir $(BIN_DIR) 2> /dev/null
#	echo '#!/bin/sh' > $@
#	echo '/bin/cat $$1 | $$2' >> $@
#	chmod a+rx $@

#
# filter
#


#enquote.$(archOS): filter.c
enquote: filter.c
	$(CC) -o enquote filter.c
	chmod a+rx $@

filter.c: filter.lex
	$(LEX) -t filter.lex > filter.c

clean:
	/bin/rm -f enquote*
