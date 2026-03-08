(* poly-init.ML - Poly/ML Bootstrap Initialization
   ===============================================

   This file provides early bootstrap initialization for Poly/ML builds.
   It loads compatibility shims and core infrastructure before the main
   HOL sources can be compiled:

   - Moscow ML compatibility layer (Mosml.sml, Binarymap, Binaryset, Listsort)
   - Path database (holpathdb)
   - Compiler-specific hooks (CompilerSpecific.ML)
   - System interface (Systeml)

   This is one of the first files loaded during HOL build and is used
   before the full kernel is available.
*)

(* this is an -*- sml -*- file *)

val _ = use "poly/Mosml.sml";
val _ = use "poly/Binarymap.sig";
val _ = use "poly/Binarymap.sml";
val _ = use "poly/Binaryset.sig";
val _ = use "poly/Binaryset.sml";
val _ = use "poly/Listsort.sig";
val _ = use "poly/Listsort.sml";
val _ = use "../src/portableML/DString.sig";
val _ = use "../src/portableML/DString.sml";
val _ = use "../src/portableML/DArray.sig";
val _ = use "../src/portableML/DArray.sml";
val _ = use "../tools/Holmake/hfs/holpathdb.sig";
val _ = use "../tools/Holmake/hfs/holpathdb.sml";
val _ = use "../tools-poly/Holmake/CompilerSpecific.ML";
val _ = use "../tools/Holmake/Systeml.sig";
val _ = use "../tools-poly/Holmake/Systeml.sml";
