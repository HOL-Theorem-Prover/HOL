EPROVER_DIR="../provers/eprover/eprover_files"

clean(){
if [ -d $1 ]; then rm -r $1; fi
mkdir $1
}
 
cd hh
clean $EPROVER_DIR
# Premise selection and translation
./hh_h4 128 ../theories ../theories/conjecture conjecture \
$EPROVER_DIR > /dev/null || \
(echo "Please run make in src/holyhammer."; exit)
# Run eprover with 128 premises
cd ../provers
sh eprover.sh
