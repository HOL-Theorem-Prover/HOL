#!/bin/sh

# write the names of all exposed structures and values within them
# specifically, 'str' or 'str.fun' when the
# corresponding structure str (or fun) exists somewhere in src/

if [ $1 ]
then
  holdir=$1
else
  holdir="../.."
fi

for path in `find $holdir/src -name "*.sig"`
do
  s=`basename $path .sig`
  echo $s
  sed -ne 's/[[:space:]]*val[[:space:]]*\([[:graph:]]\+\)[[:space:]]*:.*/'"$s"'.\1/p' $path
done
