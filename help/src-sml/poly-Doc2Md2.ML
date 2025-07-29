val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val _ = use "poly-stdprefix.ML";

fun useB f =
  (use (f ^ ".sig");
   use (f ^ ".sml"));

val _ = useB "Flash";
val _ = useB "../../src/portableML/DArray";
val _ = useB "../../sigobj/Systeml";
val _ = use "Doc2markdown2.sml";

val main = Doc2markdown2.main;
