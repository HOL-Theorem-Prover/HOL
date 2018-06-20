val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val _ = use "../../tools-poly/poly/Binarymap.sig";
val _ = use "../../tools-poly/poly/Binarymap.sml";
val _ = use "../../tools-poly/poly/Binaryset.sig";
val _ = use "../../tools-poly/poly/Binaryset.sml";
val _ = use "../../tools-poly/poly/Listsort.sig";
val _ = use "../../tools-poly/poly/Listsort.sml";
val _ = use "../../src/prekernel/stringfindreplace.sig";
val _ = use "../../src/prekernel/stringfindreplace.sml";
val _ = use "../../src/portableML/UTF8.sig";
val _ = use "../../src/portableML/UTF8.sml";
val _ = use "../../src/portableML/UnicodeChars.sig";
val _ = use "../../src/portableML/UnicodeChars.sml";

fun useB f =
  (use (f ^ ".sig");
   use (f ^ ".sml"));

val _ = useB "Flash";
val _ = useB "Symbolic";
val _ = useB "ParseDoc";
val _ = use "Doc2Tex.sml";

val main = Doc2Tex.main;
