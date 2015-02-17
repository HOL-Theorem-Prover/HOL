# Time limit and I/O files
TIM=10
DIR="vampire_files"
IN="$DIR/atp_in"
OUT="$DIR/vampire_out"
OUT1="$DIR/vampire_out1"
OUT2="$DIR/vampire_out2"
STATUS="$DIR/vampire_status" 

# Running Vampire (Executable name to be changed if you use a different version)
cd vampire
./vampire_2.6 --mode casc -t $TIM --proof tptp --output_axiom_names on $IN \
 | grep "file[(]'\| SZS" > $OUT1
# Extracting status
grep "SZS status" $OUT1 > $STATUS
sed -i -e 's/^%[ ]*SZS[ ]*status\(.*\)[ ]*for.*$/\1/' $STATUS
sed -i 's/ //g' $STATUS
# Extracting axioms
grep "file[(]" $OUT1 > $OUT2 
sed -e 's/^[ ]*file[(].*,\(.*\)[)])\..*$/\1/' $OUT2 > $OUT1
# Unescaping
grep "^a" $OUT1 > $OUT2
sed -e 's/^a\(.*\)/\1/' $OUT2 > $OUT1
sed -e 's/u_/_/g' $OUT1 > $OUT
# Cleaning
rm $OUT1
rm $OUT2
