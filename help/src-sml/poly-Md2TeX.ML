val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val _ = use "poly-stdprefix.ML";

fun useB f =
  (use (f ^ ".sig");
   use (f ^ ".sml"));

val _ = use "Md2TeX.sml";

val main = Md2TeX.main
