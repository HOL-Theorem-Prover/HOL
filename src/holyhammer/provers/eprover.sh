# Time limit and I/O files
TIM=10
DIR="eprover_files"
IN="$DIR/atp_in"
OUT1="$DIR/eprover_out1"
OUT2="$DIR/eprover_out2"
OUT="$DIR/eprover_out"
STATUS="$DIR/eprover_status"

# Running eprover with best strategy (1.8)
cd eprover
perl runepar2.pl $TIM 0 $IN 2 1 1 new_mzt_small \
 | grep "file[(]'\| SZS" > $OUT1
# Extracting status
grep "SZS status" $OUT1 > $STATUS
sed -i -e 's/^.*SZS status\(.*\).*/\1/' $STATUS
sed -i 's/ //g' $STATUS
# Extracting axioms
grep "file[(]" $OUT1 > $OUT2
sed -e 's/^fof[(].*,file[(].*,[ ]*\(.*\)[)][)]\..*$/\1/' $OUT2 > $OUT1
# Unescaping
grep "^a" $OUT1 > $OUT2
sed -e 's/^a\(.*\)/\1/' $OUT2 > $OUT1
sed -e 's/u_/_/g' $OUT1 > $OUT2
sed -e "s/i_/'/g" $OUT2 > $OUT1
sed -e 's#s_#/#g' $OUT1 > $OUT
# Cleaning
rm $OUT1
rm $OUT2
