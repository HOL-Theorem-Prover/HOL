PROVEN=$(grep -rl "Theorem" $1/*.p.status | wc -l)
TOTAL=$(ls $1/*.p.status | wc -l)
echo $PROVEN $TOTAL

