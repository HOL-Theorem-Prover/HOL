THEORY_DIR="theories"
EPROVER_DIR="provers/eprover/eprover_files"
VAMPIRE_DIR="provers/vampire/vampire_files"
Z3_DIR="provers/z3/z3_files"

clean(){
if [ -d $1 ]; then rm -r $1; fi
mkdir $1
}

clean $THEORY_DIR
clean $EPROVER_DIR
clean $VAMPIRE_DIR
clean $Z3_DIR
