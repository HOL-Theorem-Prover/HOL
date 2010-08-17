#!/bin/csh -f

set a2ml = ${ACL2_HOL_LISP}/a2ml

if ( ($#argv != 2) && ($#argv != 3)) then
	echo "Usage: $0 infile outfile [infile_dir]"
	exit 1
endif

set tmpfile = /tmp/workxxx
set infile = $argv[1]
set outfile = $argv[2]
if ( ($#argv == 3)) then
    set infile_dir = $argv[3]
else
    set infile_dir = ""
endif

rm -f $tmpfile
echo "(include-book " '"'"${a2ml}"'")' > $tmpfile
echo "(a2ml "'"'"$infile"'" "'"$outfile"'" "'"$infile_dir"'")' >> $tmpfile
echo "(value :q) (quit)" >> $tmpfile
${ACL2} < $tmpfile
