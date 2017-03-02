val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
use "../../tools-poly/poly/Binaryset.sig";
use "../../tools-poly/poly/Binaryset.sml";
use "Holdep_tokens.sig";
use "Holdep_tokens.sml";
use "holdeptool.sml";

val main = holdeptool.main
