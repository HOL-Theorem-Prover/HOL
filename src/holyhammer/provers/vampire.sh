# I/O files
DIR=$2
IN="$DIR/atp_in"
OUT="$DIR/out"
OUT1="$DIR/out1"
OUT2="$DIR/out2"
STATUS="$DIR/status"
ERROR="$DIR/error"

# Running Vampire (4.2.2)
timeout $1 ./vampire --time_limit $1 --proof tptp --output_axiom_names on $IN 2> $ERROR \
 | grep "file[(]'\| SZS" > $OUT1
# Extracting status
grep "SZS status" $OUT1 > $STATUS 2> $ERROR
sed -i -e 's/^%[ ]*SZS[ ]*status\(.*\)[ ]*for.*$/\1/' $STATUS 2> $ERROR
sed -i 's/ //g' $STATUS 2> $ERROR
# Extracting axioms
grep "^[ ]*file[(].*,\(.*\)[)])\..*$" $OUT1 > $OUT2 2> $ERROR
sed -e 's/^[ ]*file[(].*,\(.*\)[)])\..*$/\1/' $OUT2 > $OUT 2> $ERROR
