Z3_DIR="../provers/z3_files"

clean(){
if [ -d $1 ]; then rm -r $1; fi
mkdir $1
}

cd ../hh
clean $Z3_DIR
# Premise selection and translation
./hh $1 $2 ../theories ../theories/conjecture conjecture \
$Z3_DIR -thydep ../theories/thydep > /dev/null || \
(echo "See README in src/holyhammer."; exit)
# Run z3
cd ../provers
sh z3.sh $3
