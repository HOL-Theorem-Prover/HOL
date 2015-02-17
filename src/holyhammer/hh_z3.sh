# Run z3 on 32 premises
  cd hh
  # Holyhammer performs premise selection and translation
  ./hh_h4 32 ../theories ../theories/conjecture conjecture \
    ../provers/z3/z3_files > /dev/null
  cd ../provers
  echo "Running Z3 ..."
  sh z3.sh
