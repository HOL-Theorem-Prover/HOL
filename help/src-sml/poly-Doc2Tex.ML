val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val _ = use "../../tools-poly/poly/Binarymap.sig";
val _ = use "../../tools-poly/poly/Binarymap.sml";
val _ = use "../../tools-poly/poly/Binaryset.sig";
val _ = use "../../tools-poly/poly/Binaryset.sml";
val _ = use "../../tools-poly/poly/Listsort.sig";
val _ = use "../../tools-poly/poly/Listsort.sml";

fun useB f =
  (use (f ^ ".sig");
   use (f ^ ".sml"));

val _ = useB "Flash";
val _ = useB "Symbolic";
val _ = useB "ParseDoc";
val _ = use "Doc2Tex.sml";

val _ = PolyML.shareCommonData Doc2Tex.main;
val _ = PolyML.export ("Doc2Tex", Doc2Tex.main);

