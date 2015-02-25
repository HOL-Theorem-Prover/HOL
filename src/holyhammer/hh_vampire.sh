# Run vampire on 96 premises
  cd hh
  # Holyhammer performs premise selection and translation
  ./hh_h4 96 ../theories ../theories/conjecture conjecture \
    ../provers/vampire/vampire_files > /dev/null
  cd ../provers
  sh vampire.sh
