#! /bin/bash

if [ $# -lt 1 ]
then
    echo "Usage: $0 <doc-dirs-file>"
    exit 1
fi

cat $1 |
(while read docdir0
do
    docdir=../../$docdir0
    echo -n "Making ASCII version of documentation from $docdir for " >&2
    /bin/rm -f $docdir/*.adoc
    for i in $docdir/*.doc
    do
        base=$(basename $i .doc)
        dest=$docdir/$base.adoc
        if [ -f $dest ]
        then
            echo
            echo ======================================================= >&2
            echo "URK: Two help files with same name ($base) exist" >&2
            echo ======================================================= >&2
            exit 2
        else
            echo -n "$base " >&2
            sed -f gen-adoc.sed $i > $docdir/$base.adoc
        fi
    done
    echo >&2
    echo ==================== >&2
done)
