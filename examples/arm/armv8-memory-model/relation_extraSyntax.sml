structure relation_extraSyntax :> relation_extraSyntax =
struct

open HolKernel Parse boolLib bossLib
open relation_extraTheory

val ERR = mk_HOL_ERR "relation_extraSyntax"

(* - binary ---------------------------------------------------------------- *)

fun s2 n =
  HolKernel.syntax_fns
    { n = n,
      dest = HolKernel.dest_binop,
      make = fn tm => Lib.curry boolSyntax.list_mk_icomb tm o
                      Lib.list_of_pair }
    "relation_extra"

val (rcross_tm, mk_rcross, dest_rcross, is_rcross) = s2 4 "RCROSS"
val (rminus_tm, mk_rminus, dest_rminus, is_rminus) = s2 4 "RMINUS"
val (seq_tm, mk_seq, dest_seq, is_seq) = s2 4 "seq"
val (delift_tm, mk_delift, dest_delift, is_delift) = s2 4 "delift"
val (restr_rel_tm, mk_restr_rel, dest_restr_rel, is_restr_rel) =
  s2 4 "restr_rel"

(* ------------------------------------------------------------------------- *)

end
