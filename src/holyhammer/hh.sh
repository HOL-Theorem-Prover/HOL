EPROVER="provers/eprover/eprover"
VAMPIRE="provers/vampire/vampire"
Z3="provers/z3/z3"
Theorem="Theorem"

# Run eprover on 128 premises
if [ -f $EPROVER ]; then
  sh hh_eprover.sh
  EPROVER_STATUS=$(head -n 1 provers/eprover/eprover_files/eprover_status)
fi

# Run vampire on 96 premises
if [ "$EPROVER_STATUS" != "$Theorem" ] && [ -f $VAMPIRE ]; then
  sh hh_vampire.sh
  VAMPIRE_STATUS=$(head -n 1 provers/vampire/vampire_files/vampire_status)
fi

# Run z3 on 32 premises
if  [ "$EPROVER_STATUS" != "$Theorem" ] && \
    [ "$VAMPIRE_STATUS" != "$Theorem" ] && \
    [ -f $Z3 ]; then
  sh hh_z3.sh
fi
