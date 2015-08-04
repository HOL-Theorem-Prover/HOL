val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
use "../../tools-poly/poly/Binaryset.sig";
use "../../tools-poly/poly/Binaryset.sml";
use "Holdep_tokens.sig";
use "Holdep_tokens.sml";
use "holdeptool.sml";

val _ = PolyML.shareCommonData holdeptool.main
val _ = PolyML.export("holdeptool", holdeptool.main)
