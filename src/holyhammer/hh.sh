# Holyhammer (performs premise selection and translation)
VAMPIRE="provers/vampire/vampire_2.6"
Z3="provers/z3/z3-4.0"
Theorem="Theorem"

# Run eprover with 128 premises (default prover)
cd hh
./hh_h4 128 ../theories ../theories/conjecture conjecture \
../provers/eprover/eprover_files > /dev/null
cd ../provers
echo "Running Eprover ..."
sh eprover.sh
EPROVER_STATUS=$(head -n 1 eprover/eprover_files/eprover_status)
cd ..

# Run vampire on 96 premises
if [ "$EPROVER_STATUS" != "$Theorem" ] && [ -f $VAMPIRE ]; then
  cd hh
  ./hh_h4 96 ../theories ../theories/conjecture conjecture \
    ../provers/vampire/vampire_files > /dev/null
  cd ../provers
  echo "Running Vampire ..."
  sh vampire.sh
  VAMPIRE_STATUS=$(head -n 1 vampire/vampire_files/vampire_status)
  cd ..
fi

# Run z3 on 32 premises
if  [ "$EPROVER_STATUS" != "$Theorem" ] && \
    [ "$VAMPIRE_STATUS" != "$Theorem" ] && \
    [ -f $Z3 ]; then
  cd hh
  ./hh_h4 32 ../theories ../theories/conjecture conjecture \
    ../provers/z3/z3_files > /dev/null
  cd ../provers
  echo "Running Z3 ..."
  sh z3.sh
  cd ..
fi
