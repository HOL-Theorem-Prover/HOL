val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val _ = use "poly-stdprefix.ML";

fun useB f =
  (use (f ^ ".sig");
   use (f ^ ".sml"));

val _ = useB "Flash";
val _ = useB "ParseDoc";
val _ = useB "../../sigobj/Systeml";
val _ = use "Doc2Txt.sml";

val main = Doc2Txt.main;
