CT_DIR="../theories/current_theory"

clean(){
if [ -d $1 ]; then rm -r $1; fi
mkdir $1
}

clean $CT_DIR
