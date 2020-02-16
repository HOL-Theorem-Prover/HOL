# I/O files
OU=$(echo $1 | sed 's;/i/;/z3/;g')
OUT1="$OU.out1"
OUT2="$OU.out2"
OUT="$OU.core"
STATUS="$OU.status"

# Running Z3 (4.0)
timeout 60 ./z3_v4.0 -tptp DISPLAY_UNSAT_CORE=true ELIM_QUANTIFIERS=true PULL_NESTED_QUANTIFIERS=true -T:60 $1 > $OUT1
# Extracting status
grep "SZS status" $OUT1 > $STATUS
sed -i -e 's/^[ ]*SZS[ ]*status\(.*\)[ ]*for.*$/\1/' $STATUS
sed -i 's/ //g' $STATUS
# Extracting axioms
grep "^core" $OUT1 > $OUT2
sed -e 's/^core[(].*\[\(.*\)\][)].*/\1/' $OUT2 > $OUT1
tr "," "\n" < $OUT1 > $OUT2
tr -d " " < $OUT2 > $OUT
# Cleaning
rm -f $OUT1
rm -f $OUT2
