# Run eprover with 128 premises 
  cd hh
  # Holyhammer performs premise selection and translation
  ./hh_h4 128 ../theories ../theories/conjecture conjecture \
  ../provers/eprover/eprover_files > /dev/null
  cd ../provers
  sh eprover.sh
