#! /bin/bash

echo -n "Making ASCII version of documentation for " >&2
for i in $1/*.doc
do
    base=$(basename $i .doc)
    echo -n "$base " >&2
    sed -f clean-doc.sed $i > $2/$base.adoc
done
echo
