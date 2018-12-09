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
val _ = use "../../tools-poly/Holmake/Systeml.sml";
use "../../tools/Holmake/hmcore.ML";
use "../../tools/Holmake/FunctionalRecordUpdate.sml";
use "../../tools/Holmake/GetOpt.sig";
use "../../tools/Holmake/GetOpt.sml";
use "../../src/portableML/UTF8.sig";
use "../../src/portableML/UTF8.sml";
use "ugrep.sml";
