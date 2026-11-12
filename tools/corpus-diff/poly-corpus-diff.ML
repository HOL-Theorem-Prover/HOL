val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val origdir = OS.FileSys.getDir();
OS.FileSys.chDir "../../tools-poly";
val _ = use "poly/poly-init.ML";
OS.FileSys.chDir origdir;

structure BasicIO = SML90;
exception Interrupt = SML90.Interrupt

val _ = use "../../tools/Holmake/Systeml.sig"
val _ = use "../../tools/Holmake/Systeml.sml";
use "../../tools/Holmake/hmcore.ML";
use "../util/GetOpt.sig";
use "../util/GetOpt.sml";
use "corpus_diff.sml";
val main = corpus_diff.main;
