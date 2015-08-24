# I/O files
DIR="eprover_files"
IN="$DIR/atp_in"
OUT1="$DIR/eprover_out1"
OUT2="$DIR/eprover_out2"
OUT="$DIR/eprover_out"
STATUS="$DIR/eprover_status"
ERROR="$DIR/eprover_error"

# Running eprover (1.8 or 1.9)
./eprover -s --cpu-limit=$1 --auto-schedule --tptp3-in \
-R --print-statistics -p --tstp-format $IN 2> $ERROR | grep "file[(]'\|# SZS" > $OUT1
# Extracting status
grep "SZS status" $OUT1 > $STATUS 2> $ERROR
sed -i -e 's/^.*SZS status\(.*\).*/\1/' $STATUS 2> $ERROR
sed -i 's/ //g' $STATUS 2> $ERROR
# Extracting axioms
grep "file[(]" $OUT1 > $OUT2 2> $ERROR
sed -e 's/^fof[(].*file(.*,\(.*\)[)][)]\..*$/\1/' $OUT2 > $OUT1 2> $ERROR
tr -d " " < $OUT1 > $OUT 2> $ERROR
# Cleaning
rm -f $OUT1
rm -f $OUT2
