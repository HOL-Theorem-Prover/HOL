#!/bin/bash
DIR="${1:-proof_ttt}"
for i in $(find $DIR -type f); do
echo $(basename $i)
TOTAL=$(grep "Proof" $i | wc -l)
FOUND=$(grep "Proof found" $i | wc -l)
SATUR=$(grep "Proof status: Saturated" $i | wc -l)
TIMOU=$(grep "Proof status: Time Out" $i | wc -l)
echo "$TOTAL $FOUND $SATUR $TIMOU"
done

echo "Total"
TOTAL=$(grep -r "Proof" $DIR | wc -l)
FOUND=$(grep -r "Proof found" $DIR | wc -l)
SATUR=$(grep -r "Proof status: Saturated" $DIR | wc -l)
TIMOU=$(grep -r "Proof status: Time Out" $DIR | wc -l)
echo "$TOTAL $FOUND $SATUR $TIMOU"
