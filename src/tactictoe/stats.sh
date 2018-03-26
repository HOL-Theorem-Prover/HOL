cd proof_ttt
TOTAL=$(grep "Proof" $1 | wc -l)
FOUND=$(grep "Proof found" $1 | wc -l)
SATUR=$(grep "Proof status: Saturated" $1 | wc -l)
TIMOU=$(grep "Proof status: Time Out" $1 | wc -l)
echo "$TOTAL $FOUND $SATUR $TIMOU"
