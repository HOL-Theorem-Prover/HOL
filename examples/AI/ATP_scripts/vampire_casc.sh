# I/O files
OU=$(echo $1 | sed 's;/i/;/vampire_casc/;g')
OUT1="$OU.out1"
OUT2="$OU.out2"
OUT="$OU.core"
STATUS="$OU.status"

# Running Vampire (4.2.2)
timeout 60 ./vampire_v4.2.2_noz3 --mode casc --time_limit 60 --proof tptp --output_axiom_names on $1 | grep "file[(]'\| SZS" > $OUT1
# Extracting status
grep "SZS status" $OUT1 > $STATUS
sed -i -e 's/^%[ ]*SZS[ ]*status\(.*\)[ ]*for.*$/\1/' $STATUS
sed -i 's/ //g' $STATUS
# Extracting axioms
grep "^[ ]*file[(].*,\(.*\)[)])\..*$" $OUT1 > $OUT2
sed -e 's/^[ ]*file[(].*,\(.*\)[)])\..*$/\1/' $OUT2 > $OUT
