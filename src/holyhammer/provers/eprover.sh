# I/O files

DIR="$2"
IN="$DIR/atp_in"
OUT1="$DIR/out1"
OUT2="$DIR/out2"
OUT="$DIR/out"
STATUS="$DIR/status"
ERROR="$DIR/error"

# Running eprover
timeout $1 ./eprover -s --cpu-limit=$1 --auto-schedule --tptp3-in \
-R --print-statistics -p --tstp-format $IN 2> $ERROR | grep "file[(]'\|# SZS" > $OUT1 2> $ERROR
# Extracting status
grep "SZS status" $OUT1 > $STATUS 2> $ERROR
sed -i -e 's/^.*SZS status\(.*\).*/\1/' $STATUS 2> $ERROR
sed -i 's/ //g' $STATUS 2> $ERROR
# Extracting axioms
grep "^fof[(].*file(.*,\(.*\)[)][)]" $OUT1 > $OUT2 2> $ERROR
sed -e 's/^fof[(].*file(.*,\(.*\)[)][)]\..*$/\1/' $OUT2 > $OUT1 2> $ERROR
tr -d " " < $OUT1 > $OUT 2> $ERROR
# Cleaning
rm -f $OUT1
rm -f $OUT2
