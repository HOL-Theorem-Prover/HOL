ls ./$2/i/*.p | parallel -I% --max-args 1 -P $1 ./eprover_schedule.sh %

