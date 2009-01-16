#!/bin/csh -f

if ($#argv == 2) then
    set outfile = ' "'$argv[2]'"'
else if ($#argv != 1) then
    echo "Usage: $0 infile [outfile]"
    exit 1
else
    set outfile = ""
endif

set tmpfile = /tmp/workxxx
set infile = '"'$argv[1]'"'

rm -f $tmpfile

echo "(include-book " '"'"${ACL2_HOL_LISP}/book-essence"'")' > $tmpfile
echo "(book-essence $infile$outfile)" >> $tmpfile
echo "(value :q) (quit)" >> $tmpfile

${ACL2} < $tmpfile
