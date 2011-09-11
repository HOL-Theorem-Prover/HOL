structure NEWLib :> NEWLib =
struct

open HolKernel boolLib BasicProvers simpLib basic_swapTheory

val atom_ty = mk_thy_type {Thy="basic_swap",Args=[],Tyop="atom"}
val atomset_finite_t = inst [alpha |-> atom_ty] pred_setSyntax.finite_tm
fun NEW_TAC vname sort_tm (asl, g) = let
  val var = mk_var(vname, atom_ty)
  open pred_setTheory
  val (sort,tm) = pairSyntax.dest_pair sort_tm
  val fresh_thm =
      (CONV_RULE (RAND_CONV (REWRITE_CONV [IN_INSERT, IN_UNION, DE_MORGAN_THM,
                                           NOT_IN_EMPTY])) o
       SPECL [tm,sort]) new_exists
  fun is_finite_atomset t = free_in atomset_finite_t t
  val finite_asms = filter is_finite_atomset asl
  val finiteness_discharged0 =
      CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss()) (map ASSUME finite_asms)))
                fresh_thm
  val finiteness_discharged =
      MP finiteness_discharged0 TRUTH
      handle HOL_ERR _ =>
       raise mk_HOL_ERR "NEWLib" "NEW_TAC"
                        ("Finiteness discharge left with "^
                         Parse.term_to_string
                             (lhand (concl finiteness_discharged0)))
in
  X_CHOOSE_THEN var STRIP_ASSUME_TAC finiteness_discharged
end (asl, g)

(* ----------------------------------------------------------------------
    NEW_ELIM_TAC
   ---------------------------------------------------------------------- *)

fun NEW_ELIM_TAC (asl, w) = let
  val newt = find_term (can (match_term ``NEW A s``)) w
in
  CONV_TAC (UNBETA_CONV newt) THEN MATCH_MP_TAC NEW_ELIM_RULE THEN
  SIMP_TAC (srw_ss()) []
end (asl, w)

end (* struct *)
