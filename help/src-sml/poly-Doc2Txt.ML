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
val _ = useB "../../sigobj/Systeml";
val _ = use "Doc2Txt.sml";

val _ = PolyML.shareCommonData Doc2Txt.main;
val _ = PolyML.export ("Doc2Txt", Doc2Txt.main);

