CompileScript.sml : compile.lem ../semantics/lib.lem lib.lem ../semantics/miniML.lem bytecode/bytecode.lem
	lem -hol_lib ../semantics/lib.lem -hol_lib lib.lem ../semantics/miniML.lem bytecode/bytecode.lem -hol compile.lem && rm -f MiniMLScript.sml BytecodeScript.sml && sed -i 's/Pmap \$$ map/fmap/' CompileScript.sml && sed -i '4 i open fsetTheory' CompileScript.sml
