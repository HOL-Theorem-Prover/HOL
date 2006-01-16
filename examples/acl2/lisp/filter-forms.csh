#!/bin/csh -f

# This is patterned after pprint-file.csh.

# BEGIN editable variables

set acl2 = /local/scratch/mjcg/ACL2/matt/v2-9-3/saved_acl2

# set pprint_book = /local/scratch/mjcg/ACL2/matt/filter-forms
set pprint_book = /local/scratch/mjcg/HOL98/hol98/examples/acl2/lisp/filter-forms

# END editable variables

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
$acl2 < $tmpfile
