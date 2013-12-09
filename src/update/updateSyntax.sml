structure updateSyntax :> updateSyntax =
struct

open Abbrev HolKernel updateTheory

val monop =
   HolKernel.syntax_fns "update" 1 HolKernel.dest_monop
      (Lib.curry boolSyntax.mk_icomb)

val monop3 =
   HolKernel.syntax_fns "update" 3 HolKernel.dest_monop
      (Lib.curry boolSyntax.mk_icomb)

val binop =
   HolKernel.syntax_fns "update" 2 HolKernel.dest_binop HolKernel.mk_binop

val (find_tm, mk_find, dest_find, is_find) = binop "FIND"

val (override_tm, mk_override, dest_override, is_override) = monop "OVERRIDE"

val (list_update_tm, mk_list_update, dest_list_update, is_list_update) =
   monop3 "LIST_UPDATE"

val strip_list_update =
   List.map pairSyntax.dest_pair o fst o listSyntax.dest_list o dest_list_update

end
