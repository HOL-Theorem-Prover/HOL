#!/bin/csh -f

if ($#argv == 1) then
    set outfile = ' "'$argv[1]'"'
else if ($#argv != 0) then
    echo "Usage: $0 [outfile]"
    exit 1
else
    set outfile = ""
endif

set tmpfile = /tmp/workxxx

rm -f $tmpfile

echo "(include-book " '"'"${ACL2_HOL_LISP}/book-essence"'")' > $tmpfile
echo "(axioms-essence$outfile)" >> $tmpfile
echo "(value :q) (quit)" >> $tmpfile

${ACL2} < $tmpfile
