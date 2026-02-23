val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val _ = use "poly/poly-init.ML";
exception Interrupt = SML90.Interrupt
val _ = use "../tools/Holmake/Systeml.sig";
fun useC f =
    (use ("../tools/Holmake/" ^ f ^ ".sig");
     use ("../tools/Holmake/" ^ f ^ ".sml"))
fun useDeps f =
    (use ("../tools/Holmake/deps/" ^ f ^ ".sig");
     use ("../tools/Holmake/deps/" ^ f ^ ".sml"))
fun useUtil f =
    (use ("../tools/util/" ^ f ^ ".sig");
     use ("../tools/util/" ^ f ^ ".sml"))
fun useHMUtil f =
    (use ("../tools/Holmake/util/" ^ f ^ ".sig");
     use ("../tools/Holmake/util/" ^ f ^ ".sml"))

val _ = use "Holmake/Systeml.sml";
val _ = useUtil "GetOpt";
fun useHfs f =
    (use ("../tools/Holmake/hfs/" ^ f ^ ".sig");
     use ("../tools/Holmake/hfs/" ^ f ^ ".sml"))
val _ = use "../tools/Holmake/hfs/HOLFS_dtype.sml";
val _ = use "../tools/Holmake/hfs/HFS_NameMunge.sig";
val _ = use "../tools/Holmake/poly/HFS_NameMunge.sml";
val _ = useHfs "HOLFileSys";
val _ = useDeps "Holdep_tokens";
val _ = useUtil "SimpleBuffer";
fun useParsing f =
    (use ("../tools/parsing/" ^ f ^ ".sig");
     use ("../tools/parsing/" ^ f ^ ".sml"))
val _ = useParsing "AttributeSyntax";
val _ = use "../tools/parsing/HolLex.sml";
val _ = useParsing "HolParser";
val _ = useDeps "Holdep";
fun useCore f =
    (use ("../tools/Holmake/core/" ^ f ^ ".sig");
     use ("../tools/Holmake/core/" ^ f ^ ".sml"))
val _ = use "../tools/Holmake/core/Holmake_tools_dtype.sml";
val _ = use "../tools/Holmake/util/terminal_primitives.sig";
val _ = use "../tools/Holmake/util/poly-terminal-prims.ML";
val _ = useCore "Holmake_tools"
val _ = useUtil "regexpMatch"
fun useHmf f =
    (use ("../tools/Holmake/hmf/" ^ f ^ ".sig");
     use ("../tools/Holmake/hmf/" ^ f ^ ".sml"))
val _ = useHmf "parse_glob"
val _ = useHmf "internal_functions"
val _ = useHmf "Holmake_types"
val _ = useHmf "ReadHMF"
val _ = use "../tools/build/buildcline_dtype.sml"
val _ = use "../tools/util/FunctionalRecordUpdate.sml"
val _ = use "../tools/build/buildcline.sig"
val _ = use "../tools/build/buildcline.sml"
val _ = use "../tools/build/buildutils.sig";
val _ = use "../tools/build/buildutils.sml";
val _ = use "build.sml";
val main = build.main
