#!/bin/sh
# Emit a fixed number of individually identifiable lines and then fail.
# What is under test is Holmake's closing error report, so all this has
# to do is give that report something bulky and countable to quote.
i=1
while [ "$i" -le 60 ]; do
  echo "LOGLINE $1 $i"
  i=$((i + 1))
done
exit 1
