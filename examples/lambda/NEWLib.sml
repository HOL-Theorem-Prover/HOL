structure NEWLib :> NEWLib =
struct

open HolKernel Parse boolLib BasicProvers simpLib
open ncTheory

val FRESH_STRING = prove(
  ``!X Y. FINITE (X:string set) /\ Y SUBSET X ==> ~(NEW X IN Y)``,
  PROVE_TAC [pred_setTheory.SUBSET_DEF, dBTheory.NEW_FRESH_string]);

val FRESH_STRING_eq = prove(
  ``!X x. FINITE (X:string set) /\ x IN X ==> ~(NEW X = x)``,
  PROVE_TAC [pred_setTheory.SUBSET_DEF, dBTheory.NEW_FRESH_string]);

val string_ty = stringSyntax.string_ty
val strset_finite_t = inst [alpha |-> string_ty] pred_setSyntax.finite_tm
fun NEW_TAC vname t (asl, g) = let
  val var = mk_var(vname, string_ty)
  open pred_setTheory
  val fresh_thm =
      (CONV_RULE (RAND_CONV (REWRITE_CONV [IN_INSERT, IN_UNION, DE_MORGAN_THM,
                                           NOT_IN_EMPTY])) o
       SPEC t) dBTheory.FRESH_string
  fun is_finitestrset t = free_in strset_finite_t t
  val finite_asms = filter is_finitestrset asl
  val finiteness_discharged0 =
      CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss()) (map ASSUME finite_asms)))
                fresh_thm
  val finiteness_discharged = MP finiteness_discharged0 TRUTH
in
  X_CHOOSE_THEN var STRIP_ASSUME_TAC finiteness_discharged
end (asl, g)

(* ----------------------------------------------------------------------
    NEW_ELIM_TAC
   ---------------------------------------------------------------------- *)

fun NEW_ELIM_TAC (asl, w) = let
  val newt = find_term (can (match_term ``NEW (X:string set)``)) w
in
  CONV_TAC (UNBETA_CONV newt) THEN MATCH_MP_TAC NEW_ELIM_RULE THEN
  SIMP_TAC (srw_ss()) [FINITE_FV]
end (asl, w)

end (* struct *)