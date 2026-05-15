val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val _ = use "poly-stdprefix.ML";

val _ = use "AliasGen.sml";

val main = AliasGen.main
