VAMPIRE_DIR="../provers/vampire/vampire_files"

clean(){
if [ -d $1 ]; then rm -r $1; fi
mkdir $1
}

cd hh
clean $VAMPIRE_DIR 
# Premise selection and translation
./hh_h4 96 ../theories ../theories/conjecture conjecture \
$VAMPIRE_DIR > /dev/null || \
(echo "Please run make in src/holyhammer."; exit)
# Run vampire on 96 premises
cd ../provers
sh vampire.sh
