THEORY_DIR="../theories"

clean(){
if [ -d $1 ]; then rm -r $1; fi
mkdir $1
}

clean $THEORY_DIR
