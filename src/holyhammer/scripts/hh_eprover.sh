EPROVER_DIR="../provers/eprover_files"

clean(){
if [ -d $1 ]; then rm -r $1; fi
mkdir $1
}

cd ../hh
clean $EPROVER_DIR
# Premise selection and translation
./hh $1 $2 ../theories ../theories/conjecture conjecture \
$EPROVER_DIR -thydep ../theories/thydep > /dev/null || \
(echo "See README in src/holyhammer."; exit)
# Run eprover
cd ../provers
sh eprover.sh $3
