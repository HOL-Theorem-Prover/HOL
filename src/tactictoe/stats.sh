TOTAL=$(ls eval/"$1"/buildheap_* | wc -l)
PROVEN=$(grep -r "tactictoe: proven" eval/"$1"/buildheap_* | wc -l)
TIMEOUT=$(grep -r "tactictoe: timeout" eval/"$1"/buildheap_* | wc -l)
SATURATED=$(grep -r "tactictoe: saturated" eval/"$1"/buildheap_* | wc -l)
echo "$TOTAL problems: $PROVEN proven, $TIMEOUT timeout, $SATURATED saturated" 
