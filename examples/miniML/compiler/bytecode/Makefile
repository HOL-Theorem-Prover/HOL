BytecodeScript.sml : bytecode.lem
	lem -hol_lib ../lib.lem -hol bytecode.lem &&\
sed -i 's/Pmap \$$ map/fmap/g' $@
