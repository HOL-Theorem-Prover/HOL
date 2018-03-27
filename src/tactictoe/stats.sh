for i in $(find $1 -type f); do
echo $(basename $i)
TOTAL=$(grep "Proof" $i | wc -l)
FOUND=$(grep "Proof found" $i | wc -l)
SATUR=$(grep "Proof status: Saturated" $i | wc -l)
TIMOU=$(grep "Proof status: Time Out" $i | wc -l)
echo "$TOTAL $FOUND $SATUR $TIMOU"
done

echo "Total"
TOTAL=$(grep -r "Proof" $1 | wc -l)
FOUND=$(grep -r "Proof found" $1 | wc -l)
SATUR=$(grep -r "Proof status: Saturated" $1 | wc -l)
TIMOU=$(grep -r "Proof status: Time Out" $1 | wc -l)
