# Run eprover with 128 premises 
  cd hh
  ./hh_h4 128 ../theories ../theories/conjecture conjecture \
  ../provers/eprover/eprover_files > /dev/null
  cd ../provers
  echo "Running Eprover ..."
  sh eprover.sh
