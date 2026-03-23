all:
	Holmake
	cp ../../../examples/acl2/lisp/untranslate-file.lisp .
	echo "(certify-book \"untranslate-file\")" | acl2
	cat session1.lisp | acl2
	cat session2.lisp | acl2
	cat fact-out.lisp
clean:
	Holmake cleanAll
	/bin/rm fact.lisp fact-out.* untranslate-file.* 
