#!/bin/sh

# write the names of all existing doc files:
# specifically, 'str' or 'str.fun' when the
# corresponding Docfiles/str.fun.doc exists

if [ $1 ]
then
  holdir=$1
else
  holdir="../.."
fi

ls -1 $holdir/help/Docfiles/*.doc | sed 's/.*s\/\([^/]\+\)\.doc/\1/'
