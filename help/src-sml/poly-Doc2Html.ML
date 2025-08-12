val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val _ = use "poly-stdprefix.ML";

fun useB f =
  (use (f ^ ".sig");
   use (f ^ ".sml"));

val _ = useB "Flash";
val _ = useB "../../sigobj/Systeml";
val _ = use "../../tools-poly/poly/Mosml.sml";
val _ = use "SHA1_MLshim.sig";
val _ = use "../../src/portableML/poly/SHA1_ML.sml";
val _ = use "Doc2Html.sml";

val main = Doc2Html.main
