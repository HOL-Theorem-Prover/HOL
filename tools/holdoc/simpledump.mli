(* straightforward literal dumper - renders everything to
   the obvious string, except for directives which are
   processed as appropriate and elided. *)

val dumptexdoc : Holdocmodel.texdoc -> string
val dumptexdoc_content : Holdocmodel.texdoc_content -> string
val dumptextdoc : Holdocmodel.textdoc -> string
val dumptextdoc_content : Holdocmodel.textdoc_content -> string
val dumpmosmldoc :
  Holdocmodel.mosml_content list *
  (int * Holdocmodel.mosml_content list) list -> string
val dumpmosml_line : Holdocmodel.mosml_content list -> string
val dumpmosml_content : Holdocmodel.mosml_content -> string
val dumpholdoc : Holdocmodel.holdoc -> string
val dumphol_line : Holdocmodel.hol_line -> string
val dumphol_content : Holdocmodel.hol_content -> string
val dumpdirective : Holdocmodel.directive -> string
val dumpdirective_content : Holdocmodel.directive -> string
