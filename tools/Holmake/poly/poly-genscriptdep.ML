val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val origdir = OS.FileSys.getDir();
OS.FileSys.chDir "../../../tools-poly";
val _ = use "poly/poly-init.ML";
OS.FileSys.chDir origdir;

structure BasicIO = SML90;
exception Interrupt = SML90.Interrupt

fun useC f = (use ("../" ^ f ^ ".sig"); use ("../" ^ f ^ ".sml"))

fun useS f = use ("../" ^ f ^ ".sml")

val _ = use "../Systeml.sig"
val _ = use "../../../tools-poly/Holmake/Systeml.sml";

val _ = use "../hmcore.ML";

val _ = use "genscriptdep.sml";

fun main() = genscriptdep.main()
