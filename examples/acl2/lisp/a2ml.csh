#!/bin/csh -f

# BEGIN editable variables

# set acl2 = /usr/bin/acl2

set acl2 = /local/scratch/mjcg/ACL2/matt/v2-9-3/saved_acl2
set a2ml = /local/scratch/mjcg/HOL98/hol98/examples/acl2/lisp/a2ml

# END editable variables

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
$acl2 < $tmpfile
