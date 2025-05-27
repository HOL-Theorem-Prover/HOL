val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
use "../../tools-poly/poly/Binaryset.sig";
use "../../tools-poly/poly/Binaryset.sml";
use "../../tools-poly/poly/Binarymap.sig";
use "../../tools-poly/poly/Binarymap.sml";
use "HOLFS_dtype.sml";
use "HFS_NameMunge.sig";
use "poly/HFS_NameMunge.sml";
use "HOLFileSys.sig";
use "HOLFileSys.sml";
use "Holdep_tokens.sig";
use "Holdep_tokens.sml";
use "Systeml.sig";
use "../../tools-poly/Holmake/Systeml.sml";
use "AttributeSyntax.sig";
use "AttributeSyntax.sml";
use "HolLex.sml";
use "HolParser.sig";
use "HolParser.sml";
use "holdeptool.sml";

val main = holdeptool.main
