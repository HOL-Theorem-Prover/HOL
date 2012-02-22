all:
	Holmake
clean:
	Holmake cleanAll
	cd lisp-runtime && Holmake cleanAll && cd ..
	cd lisp-runtime/bytecode && Holmake cleanAll && cd ../..
	cd lisp-runtime/garbage-collector && Holmake cleanAll && cd ../..
	cd lisp-runtime/implementation && Holmake cleanAll && cd ../..
	cd lisp-runtime/parse && Holmake cleanAll && cd ../..
	cd lisp-runtime/spec && Holmake cleanAll && cd ../..
	cd lisp-runtime/extract && Holmake cleanAll && cd ../..
	cd milawa-prover && Holmake cleanAll && cd ..
	cd milawa-prover/soundness-thm && Holmake cleanAll && cd ../..
