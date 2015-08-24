VAMPIRE_DIR="../provers/vampire_files"

clean(){
if [ -d $1 ]; then rm -r $1; fi
mkdir $1
}

cd ../hh
clean $VAMPIRE_DIR
# Premise selection and translation
./hh $1 $2 ../theories ../theories/conjecture conjecture \
$VAMPIRE_DIR -thydep ../theories/thydep > /dev/null || \
(echo "See README in src/holyhammer."; exit)
# Run vampire
cd ../provers
sh vampire.sh $3
