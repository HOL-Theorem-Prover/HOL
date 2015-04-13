# Time limit and I/O files
TIM=10
DIR="z3_files"
IN="$DIR/atp_in"
OUT1="$DIR/z3_out1"
OUT2="$DIR/z3_out2"
OUT="$DIR/z3_out"
STATUS="$DIR/z3_status"

# Running Z3 (4.0)
cd z3
./z3 -tptp DISPLAY_UNSAT_CORE=true ELIM_QUANTIFIERS=true PULL_NESTED_QUANTIFIERS=true \
-T:$TIM $IN > $OUT1 2> /dev/null
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
rm $OUT1
rm $OUT2
