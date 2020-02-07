# I/O files
OU=$(echo $1 | sed 's;/i/;/o/;g')
OUT1="$OU.out1"
OUT2="$OU.out2"
OUT="$OU.core"
STATUS="$OU.status"

# Running eprover
timeout 10 ./eprover -s --cpu-limit=10 --auto-schedule --tptp3-in \
-R --print-statistics -p --tstp-format $1 | grep "file[(]'\|# SZS" > $OUT1
# Extracting status
grep "SZS status" $OUT1 > $STATUS
sed -i -e 's/^.*SZS status\(.*\).*/\1/' $STATUS
sed -i 's/ //g' $STATUS
# Extracting axioms
grep "^fof[(].*file(.*,\(.*\)[)][)]" $OUT1 > $OUT2
sed -e 's/^fof[(].*file(.*,\(.*\)[)][)]\..*$/\1/' $OUT2 > $OUT1
tr -d " " < $OUT1 > $OUT
# Cleaning
rm -f $OUT1
rm -f $OUT2
