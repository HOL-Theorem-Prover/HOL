structure newtypeTools :> newtypeTools =
struct

open Abbrev HolKernel boolLib

infixr 6 /\
infixr 5 ==>
infix  9 ==
fun t1 /\ t2 = mk_conj(t1, t2)
fun t1 ==> t2 = mk_imp (t1,t2)
fun t1 == t2 = mk_eq(t1,t2)


fun rich_new_type (tyname, exthm) = let
  val bij_ax = new_type_definition(tyname, exthm)
  val (termP, oldty) = let
    val (bvar, exthm_body) = exthm |> concl |> dest_exists
  in
    (rator exthm_body, type_of bvar)
  end
  fun termPf x = mk_comb(termP, x)
  val oldty = exthm |> concl |> dest_exists |> #1 |> type_of
  val x = mk_var("x", oldty) and y = mk_var("y", oldty)
  val newty = bij_ax |> concl |> dest_exists |> #1 |> type_of |> dom_rng |> #1
  val term_ABSREP =
      define_new_type_bijections { ABS = tyname ^ "_ABS", REP = tyname ^ "_REP",
                                   name = tyname ^ "_ABSREP", tyax = bij_ax}
  val absrep_id = term_ABSREP |> CONJUNCT1
  val (term_ABS_t, term_REP_t) = let
    val eqn1_lhs = absrep_id|> concl |> strip_forall |> #2 |> lhs
    val (a, x) = dest_comb eqn1_lhs
  in
    (a, rator x)
  end
  fun term_ABSf x = mk_comb(term_ABS_t, x)
  fun term_REPf x = mk_comb(term_REP_t, x)
  val g = mk_var("g", newty) and h = mk_var("h", newty)
  val term_ABS_pseudo11 = prove(
    termPf x /\ termPf y ==> (term_ABSf x == term_ABSf y) == (x == y),
    STRIP_TAC THEN EQ_TAC THENL [
      ALL_TAC, DISCH_THEN SUBST1_TAC THEN REFL_TAC] THEN
    DISCH_THEN (MP_TAC o AP_TERM term_REP_t) THEN
    REPEAT (POP_ASSUM (SUBST1_TAC o
                       CONV_RULE (REWR_CONV (CONJUNCT2 term_ABSREP)))) THEN
    REWRITE_TAC [])
  val term_REP_11 = prove(
    (term_REPf g == term_REPf h) == (g == h),
    EQ_TAC THENL [ALL_TAC, DISCH_THEN SUBST1_TAC THEN REFL_TAC] THEN
    DISCH_THEN (MP_TAC o AP_TERM term_ABS_t) THEN REWRITE_TAC [absrep_id])
  val termP_term_REP = prove(
    termPf (term_REPf g),
    CONV_TAC (REWR_CONV (CONJUNCT2 term_ABSREP) THENC
              LAND_CONV (RAND_CONV (REWR_CONV absrep_id))) THEN
    REFL_TAC)
  val termP_exists = prove(
    termPf x == mk_exists(g, x == term_REPf g),
    EQ_TAC THENL [
      REWRITE_TAC [CONJUNCT2 term_ABSREP] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      EXISTS_TAC (term_ABSf x) THEN REFL_TAC,
      DISCH_THEN (X_CHOOSE_THEN g SUBST1_TAC) THEN
      CONV_TAC (REWR_CONV (EQT_INTRO termP_term_REP))
    ])
  val repabs_pseudo_id =
      term_ABSREP |> CONJUNCT2 |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GEN_ALL
in
  {term_ABS_pseudo11 = term_ABS_pseudo11,
   term_REP_11 = term_REP_11, repabs_pseudo_id = repabs_pseudo_id,
   absrep_id = absrep_id,
   termP_term_REP = termP_term_REP,
   termP_exists = termP_exists,
   newty = newty,
   termP = termP,
   term_REP_t = term_REP_t, term_ABS_t = term_ABS_t}
end


end (* struct *)
