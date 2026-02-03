val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
use "../../../tools-poly/poly/Binaryset.sig";
use "../../../tools-poly/poly/Binaryset.sml";
use "../../../tools-poly/poly/Binarymap.sig";
use "../../../tools-poly/poly/Binarymap.sml";
use "../HOLFS_dtype.sml";
use "../HFS_NameMunge.sig";
use "HFS_NameMunge.sml";
use "../HOLFileSys.sig";
use "../HOLFileSys.sml";
use "../deps/Holdep_tokens.sig";
use "../deps/Holdep_tokens.sml";
use "../Systeml.sig";
use "../../../tools-poly/Holmake/Systeml.sml";
use "../../parsing/AttributeSyntax.sig";
use "../../parsing/AttributeSyntax.sml";
use "../../parsing/HolLex.sml";
use "../../parsing/HolParser.sig";
use "../../parsing/HolParser.sml";
use "../deps/holdeptool.sml";

val main = holdeptool.main
