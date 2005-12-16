#!/bin/csh -f

# BEGIN editable variables

# set acl2 = /usr/bin/acl2

set acl2 = /local/scratch/mjcg/ACL2/matt/v2-9-3/saved_acl2
set pprint_book = /local/scratch/mjcg/HOL98/hol98/examples/acl2/lisp/pprint-file
set patch_dir = /local/scratch/mjcg/HOL98/hol98/examples/acl2/lisp

# END editable variables

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
    echo '(load "${patch_dir}/patch.lisp")' >> $tmpfile
    echo '(acl2-compile-file "${patch_dir}/patch.lisp" "${patch_dir}/patch.lisp")' >> $tmpfile
    echo '(load "${patch_dir}/patch")' >> $tmpfile
    echo '(lp)' >> $tmpfile
endif

echo '(pprint-file' '"'$infile'"' '"'$outfile'"' $opt ')'  >> $tmpfile
$acl2 < $tmpfile >&/dev/null
$acl2 < $tmpfile
