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
val _ = useC "GetOpt";
val _ = use "../tools/Holmake/HOLFS_dtype.sml";
val _ = use "../tools/Holmake/HFS_NameMunge.sig";
val _ = use "../tools/Holmake/poly/HFS_NameMunge.sml";
val _ = useC "HOLFileSys";
val _ = useC "Holdep_tokens";
val _ = useC "HM_SimpleBuffer";
val _ = useC "AttributeSyntax";
val _ = use "../tools/Holmake/HolLex.sml";
val _ = useC "HolParser";
val _ = useC "Holdep";
val _ = use "../tools/Holmake/Holmake_tools_dtype.sml";
val _ = use "../tools/Holmake/terminal_primitives.sig";
val _ = use "../tools/Holmake/poly-terminal-prims.ML";
val _ = useC "Holmake_tools"
val _ = useC "regexpMatch"
val _ = useC "parse_glob"
val _ = useC "internal_functions"
val _ = useC "Holmake_types"
val _ = useC "ReadHMF"
val _ = use "../tools/buildcline_dtype.sml"
val _ = use "../tools/Holmake/FunctionalRecordUpdate.sml"
val _ = useC "../buildcline"
val _ = use "../tools/buildutils.sig";
val _ = use "../tools/buildutils.sml";
val _ = use "build.sml";
val main = build.main
