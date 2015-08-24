# I/O files
DIR="vampire_files"
IN="$DIR/atp_in"
OUT="$DIR/vampire_out"
OUT1="$DIR/vampire_out1"
OUT2="$DIR/vampire_out2"
STATUS="$DIR/vampire_status"
ERROR="$DIR/vampire_error"

# Running Vampire (2.6)
./vampire --mode casc -t $1 --proof tptp --output_axiom_names on $IN 2> $ERROR \
 | grep "file[(]'\| SZS" > $OUT1
# Extracting status
grep "SZS status" $OUT1 > $STATUS 2> $ERROR
sed -i -e 's/^%[ ]*SZS[ ]*status\(.*\)[ ]*for.*$/\1/' $STATUS 2> $ERROR
sed -i 's/ //g' $STATUS 2> $ERROR
# Extracting axioms
grep "file[(]" $OUT1 > $OUT2 2> $ERROR
sed -e 's/^[ ]*file[(].*,\(.*\)[)])\..*$/\1/' $OUT2 > $OUT 2> $ERROR
# Cleaning
rm -f $OUT1
rm -f $OUT2
