#!/bin/csh -f

set pprint_book = ${ACL2_HOL_LISP}/pprint-file

set opt = ""

if ($#argv == 3) then
    set opt = nil
else if ($#argv != 2) then
    echo "Usage: $0 infile outfile any"
    echo "       where 'any' should be supplied when translating parts of axioms.lisp"
    exit 1
endif

set tmpfile = /tmp/workxxx
set infile = $argv[1]
set outfile = $argv[2]

rm -f $tmpfile
echo "(include-book " '"'"${pprint_book}"'")' > $tmpfile

if ($opt != "") then
    echo ':q' >> $tmpfile
    echo '(setf (cadr (assoc (quote global-value) (get (quote untouchables) *current-acl2-world-key*))) nil)' >> $tmpfile
    echo '(lp)' >> $tmpfile
endif

echo '(pprint-file' '"'$infile'"' '"'$outfile'"' $opt ')'  >> $tmpfile
# ${ACL2} < $tmpfile >&/dev/null
${ACL2} < $tmpfile
