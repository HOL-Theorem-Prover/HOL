# Run vampire on 96 premises
  cd hh
  ./hh_h4 96 ../theories ../theories/conjecture conjecture \
    ../provers/vampire/vampire_files > /dev/null
  cd ../provers
  echo "Running Vampire ..."
  sh vampire.sh
