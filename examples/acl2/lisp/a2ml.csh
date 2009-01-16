#!/bin/csh -f

set a2ml = ${ACL2_HOL_LISP}/a2ml

if ($#argv != 2) then
	echo "Usage: $0 infile outfile"
	exit 1
endif

set tmpfile = /tmp/workxxx
set infile = $argv[1]
set outfile = $argv[2]

rm -f $tmpfile
echo "(include-book " '"'"${a2ml}"'")' > $tmpfile
echo "(a2ml "'"'"$infile"'" "'"$outfile"'")' >> $tmpfile
echo "(value :q) (quit)" >> $tmpfile
${ACL2} < $tmpfile
