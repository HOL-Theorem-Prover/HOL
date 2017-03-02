val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val _ = use "poly/poly-init.ML";
exception Interrupt = SML90.Interrupt
val _ = use "../tools/Holmake/Systeml.sig";
fun useC f =
    (use ("../tools/Holmake/" ^ f ^ ".sig");
     use ("../tools/Holmake/" ^ f ^ ".sml"))

val _ = use "Holmake/Systeml.sml";
val _ = useC "Holdep_tokens";
val _ = useC "Holdep";
val _ = useC "Holmake_tools"
val _ = useC "regexpMatch"
val _ = useC "parse_glob"
val _ = useC "internal_functions"
val _ = useC "Holmake_types"
val _ = useC "ReadHMF"
val _ = use "../tools/buildutils.sig";
val _ = use "../tools/buildutils.sml";
val _ = use "build.sml";
val main = build.main
