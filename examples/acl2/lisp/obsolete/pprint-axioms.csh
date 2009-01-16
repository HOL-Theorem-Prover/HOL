#!/bin/csh -f

# This is patterned after pprint-file.csh.

# For quiet operation:
# ./pprint-axioms.csh > /dev/null

set pprint_book = ${ACL2_HOL_LISP}/pprint-axioms

if ($#argv == 0) then
    set outfile = ""
else if ($#argv == 1) then
    set outfile = '"'$argv[1]'"'
else
    echo "Usage: $0 outfile"
    exit 1
endif

set tmpfile = /tmp/workxxx

rm -f $tmpfile
echo "(include-book " '"'"${pprint_book}"'")' > $tmpfile
echo "(pprint-axioms $outfile)"  >> $tmpfile
${ACL2} < $tmpfile
