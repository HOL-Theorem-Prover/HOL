BytecodeScript.sml : bytecode.lem
	lem -hol bytecode.lem &&\
sed -i 's/Pmap \$$ map/fmap/g' $@ &&\
sed -i 's/Hol \$$ //g' $@ &&\
sed -i 's/Hol \$$(::)/CONS /g' $@ &&\
sed -i 's/Hol \$$(\([^)]\+\))/($$\1)/g' $@ &&\
sed -i 's/Hol \$$\&/\&/g' $@
