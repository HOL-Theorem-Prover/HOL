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

val _ = useC "Holdep_tokens";
val _ = use "../FNameToUnquotedDeps.sig";
val _ = useS "mosml/FNameToUnquotedDeps";
val _ = useC "Holdep";

val _ = useC "regexpMatch";
val _ = useC "parse_glob";
val _ = useC "internal_functions";
val _ = useC "tailbuffer";
val _ = useC "Holmake_tools";
val _ = useC "Holmake_types";
val _ = useC "ReadHMF";
val _ = useC "GetOpt";
val _ = useS "FunctionalRecordUpdate";
val _ = useC "HM_Core_Cline";
val _ = useC "HM_DepGraph";
val _ = useC "HM_GraphBuildJ1";
val _ = useC "poly/HM_Cline";
val _ = useC "poly/HM_BaseEnv";
val _ = use  "../BuildCommand.sig";
val _ = useC "poly/ProcessMultiplexor";
val _ = useC "poly/MB_Monitor";
val _ = useS "poly/multibuild";
val _ = useS "poly/BuildCommand";
val _ = useS "Holmake";

val die_with = Holmake.die_with

fun main() =
  Holmake.main()
  handle SML90.Interrupt => die_with "Holmake interrupted"
       | e => die_with ("Holmake failed with exception: "^
                          exnMessage e)
