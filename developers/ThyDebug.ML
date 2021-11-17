(* Use an invocation such as

     buildheap developers/ThyDebug.ML sometheory.uo

   possibly with an additional -b to specify the base heap, and/or a
   --repl to get dropped into a REPL once sometheory is loaded.

   Note that a REPL will be bereft of nice pretty-printers if
   tools-poly/prelude.ML is not also added to the object file list.

*)
val _ = Globals.print_thy_loads := true;
val _ = Meta.meta_debug := true;
