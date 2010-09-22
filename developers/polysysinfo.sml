val _ = PolyML.print_depth 0;
val version_string_w1 =
    hd (String.tokens Char.isSpace PolyML.Compiler.compilerVersion)
    handle Empty => ""
val compiler_number =
    Real.floor (100.0 * valOf (Real.fromString version_string_w1))
    handle Option => 0
val _ = print ("\nMLSYSTEM = poly"^Int.toString compiler_number^"\n");

