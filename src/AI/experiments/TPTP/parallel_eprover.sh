cat $2 | parallel -I% --max-args 1 -P $1 ./eprover.sh %

