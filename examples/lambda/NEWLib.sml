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

fun NEW_TAC vname t = let
  val var = mk_var(vname, ``:string``)
  val new_t = mk_comb(``NEW:string set -> string``, t)
  val asm = mk_eq(var, new_t)
  fun union_inds (sets, inds) t = let
    val (f, args) = strip_comb t
  in
    if same_const f pred_setSyntax.union_tm then
      union_inds (union_inds (sets, inds) (hd args)) (hd (tl args))
    else if same_const f pred_setSyntax.insert_tm then
      union_inds (sets, hd args::inds) (hd (tl args))
    else if same_const f pred_setSyntax.empty_tm then (sets, inds)
    else (t::sets, inds)
  end
  val (sets, inds) = union_inds ([], []) t
  val munge = UNDISCH o CONV_RULE (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
  fun mk_IN (v,s) = let
    val ty = type_of v
  in
    list_mk_comb(inst [alpha |-> ty] pred_setSyntax.in_tm, [v,s])
  end
  fun prove_ind i =
      munge (SIMP_PROVE (srw_ss()) [FRESH_STRING_eq]
                        (mk_imp(asm, mk_neg(mk_eq(var, i)))))
  fun prove_set s =
      munge (prove(mk_imp(asm, mk_neg(mk_IN(var, s))),
                   DISCH_THEN SUBST_ALL_TAC THEN
                   MATCH_MP_TAC FRESH_STRING THEN
                   SIMP_TAC (srw_ss()) [pred_setTheory.SUBSET_DEF]))
in
  Q.ABBREV_TAC `^asm` THEN
  MAP_EVERY (ASSUME_TAC o prove_ind) inds THEN
  MAP_EVERY (ASSUME_TAC o prove_set) sets THEN
  Q.RM_ABBREV_TAC `^var`
end

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