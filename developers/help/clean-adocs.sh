#! /bin/bash

if [ $# -ne 1 ]
then
    echo "Usage: $0 <docdir specifying file>" >&2
    exit 1
fi

cat $1 | (
 while read docdir
 do
    echo "Cleaning out ../../$docdir"
    /bin/rm -f ../../$docdir/*.adoc
 done
)