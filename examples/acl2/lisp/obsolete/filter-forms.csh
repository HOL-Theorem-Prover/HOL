#!/bin/csh -f

# This is patterned after pprint-file.csh.

set pprint_book = ${ACL2_HOL_LISP}/filter-forms

if ($#argv != 2) then
    echo "Usage: $0 infile outfile"
    exit 1
endif

set tmpfile = /tmp/workxxx
set infile = $argv[1]
set outfile = $argv[2]

rm -f $tmpfile
echo "(include-book " '"'"${pprint_book}"'")' > $tmpfile
echo '(acl2::ld' '"'${infile}'" :ld-error-action :return :ld-skip-proofsp t)' >> $tmpfile
echo '(write-forms' '"'$infile'"' '"'$outfile'"' 'nil state)'  >> $tmpfile
${ACL2} < $tmpfile
