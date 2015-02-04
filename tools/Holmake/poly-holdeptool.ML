val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
use "../../tools-poly/poly/Binaryset.sig";
use "../../tools-poly/poly/Binaryset.sml";
use "SourcePos.sig";
use "SourcePos.sml";
use "SourceFile.sig";
use "SourceFile.sml";
use "Region.sig";
use "Region.sml";
use "Holdep_tokens.lex.sml";
use "holdeptool.sml";

val _ = PolyML.shareCommonData holdeptool.main
val _ = PolyML.export("holdeptool", holdeptool.main)
