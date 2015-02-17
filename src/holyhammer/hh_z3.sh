# Run z3 on 32 premises
  cd hh
  ./hh_h4 32 ../theories ../theories/conjecture conjecture \
    ../provers/z3/z3_files > /dev/null
  cd ../provers
  echo "Running Z3 ..."
  sh z3.sh
