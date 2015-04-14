# Time limit and I/O files
TIM=10
DIR="vampire_files"
IN="$DIR/atp_in"
OUT="$DIR/vampire_out"
OUT1="$DIR/vampire_out1"
OUT2="$DIR/vampire_out2"
STATUS="$DIR/vampire_status"
ERROR="$DIR/vampire_error"

# Running Vampire (2.6)
cd vampire
./vampire --mode casc -t $TIM --proof tptp --output_axiom_names on $IN \
 | grep "file[(]'\| SZS" > $OUT1 2> $ERROR
# Extracting status
grep "SZS status" $OUT1 > $STATUS
sed -i -e 's/^%[ ]*SZS[ ]*status\(.*\)[ ]*for.*$/\1/' $STATUS
sed -i 's/ //g' $STATUS
# Extracting axioms
grep "file[(]" $OUT1 > $OUT2
sed -e 's/^[ ]*file[(].*,\(.*\)[)])\..*$/\1/' $OUT2 > $OUT
# Cleaning
rm $OUT1
rm $OUT2
