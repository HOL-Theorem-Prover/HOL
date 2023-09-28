open HolKernel Parse boolLib bossLib pred_setTheory relationTheory set_relationTheory prim_recTheory

open generalHelpersTheory wordTheory

val _ = new_theory "ltl"
val _ = ParseExtras.temp_loose_equality()

val _ = Datatype`
  ltl_frml
  = VAR 'a
  | N_VAR 'a
  | DISJ ltl_frml ltl_frml
  | CONJ ltl_frml ltl_frml
  | X ltl_frml
  | U ltl_frml ltl_frml
  | R ltl_frml ltl_frml`;

val MODELS_def =
  Define
    `(MODELS w (VAR a) = (a IN (at w 0)))
  /\ (MODELS w (N_VAR a) = ~(a IN (at w 0)))
  /\ (MODELS w (DISJ f1 f2) = (MODELS w f1) \/ (MODELS w f2))
  /\ (MODELS w (CONJ f1 f2) = (MODELS w f1) /\ (MODELS w f2))
  /\ (MODELS w (X f) = (MODELS (suff w 1) f))
  /\ (MODELS w (U f1 f2) =
        ?n. (MODELS (suff w n) f2) /\ !i. (i < n) ==> (MODELS (suff w i) f1))
  /\ (MODELS w (R f1 f2) =
        !n. (MODELS (suff w n) f2) \/ ?i. (i < n) /\ (MODELS (suff w i) f1))`;

val R_COND_LEMM = store_thm
  ("R_COND_LEMM",
   ``!w f1 f2. (!n. (MODELS (suff w n) f2) \/ ?i. (i < n) /\ (MODELS (suff w i) f1))
      = ((!n. MODELS (suff w n) f2) \/
         ?n. MODELS (suff w n) f1 /\ !i. i <= n ==> MODELS (suff w i) f2)``,
   rpt strip_tac >> rw[EQ_IMP_THM]
    >- (Cases_on `!n. MODELS (suff w n) f2` >> fs[]
        >> qabbrev_tac `N = LEAST n. ~MODELS (suff w n) f2`
        >> `(!i. i < N ==> MODELS (suff w i) f2) ∧ ~MODELS (suff w N) f2` by (
             simp[Abbr `N`] >> numLib.LEAST_ELIM_TAC
             >> simp[] >> metis_tac[]
         )
        >> disj2_tac
        >> `MODELS (suff w N) f2 ∨ ∃i. i < N ∧ MODELS (suff w i) f1` by metis_tac[]
        >> qexists_tac `i` >> fs[]
       )
    >- metis_tac[]
    >- (Cases_on `n' <= n`
      >- metis_tac[]
      >- (`n < n'` by simp[] >> metis_tac[])
       )
  );

val TRUE_def = Define `TRUE = DISJ (VAR ARB) (N_VAR ARB)`;
val FALSE_def = Define `FALSE = CONJ (VAR ARB) (N_VAR ARB)`;

(*

  Subformulae

*)

val subForms_def = Define
    `  (subForms (VAR a) = {VAR a})
    /\ (subForms (N_VAR a) = {N_VAR a})
    /\ (subForms (DISJ f1 f2) = {DISJ f1 f2} ∪ (subForms f1) ∪ (subForms f2))
    /\ (subForms (CONJ f1 f2) = {CONJ f1 f2} ∪ (subForms f1) ∪ (subForms f2))
    /\ (subForms (X f) = {X f} ∪ (subForms f))
    /\ (subForms (U f1 f2) = {U f1 f2} ∪ (subForms f1) ∪ (subForms f2))
    /\ (subForms (R f1 f2) = {R f1 f2} ∪ (subForms f1) ∪ (subForms f2))`;

val SUBFORMS_REFL = store_thm
  ("SUBFORMS_REFL",
   ``!f. f ∈ subForms f``,
   Induct_on `f` >> simp[subForms_def]);

val SUBFORMS_TRANS = store_thm
  ("SUBFORMS_TRANS",
  ``!f1 f2 f3. f1 ∈ subForms f2 /\ f2 ∈ subForms f3 ==> f1 ∈ subForms f3``,
  Induct_on `f3` >> rpt strip_tac >> dsimp[] >> fs[subForms_def, UNION_DEF]
  >> fs[subForms_def, UNION_DEF]
  >> metis_tac[]
  );

val no_tmp_op_def = Define
`(no_tmp_op (VAR a) = 1)
    /\ (no_tmp_op (N_VAR a) = 1)
    /\ (no_tmp_op (DISJ f1 f2) = (no_tmp_op f1) + (no_tmp_op f2))
    /\ (no_tmp_op (CONJ f1 f2) = (no_tmp_op f1) + (no_tmp_op f2))
    /\ (no_tmp_op (X f) = (no_tmp_op f) + 1)
    /\ (no_tmp_op (U f1 f2) =(no_tmp_op f1) + (no_tmp_op f2) +1)
    /\ (no_tmp_op (R f1 f2) =(no_tmp_op f1) + (no_tmp_op f2) +1)`;

val NO_TMP_LEMM = store_thm
  ("NO_TMP_LEMM", ``!f. no_tmp_op f >= 1``,
    Induct_on `f` >> simp[no_tmp_op_def]);

val TMP_OP_DECR_WITH_SF = store_thm
  ("TMP_OP_DECR_WITH_SF",
   ``!f f'. (f' ∈ subForms f ==> (no_tmp_op f' <= no_tmp_op f))``,
   Induct_on `f` >> fs[subForms_def, no_tmp_op_def] >> rpt strip_tac
   >> simp[no_tmp_op_def]
   >- (`no_tmp_op f'' <= no_tmp_op f` by metis_tac[] >> simp[])
   >- (`no_tmp_op f'' <= no_tmp_op f'` by metis_tac[] >> simp[])
   >- (`no_tmp_op f'' <= no_tmp_op f` by metis_tac[] >> simp[])
   >- (`no_tmp_op f'' <= no_tmp_op f'` by metis_tac[] >> simp[])
   >- (`no_tmp_op f' <= no_tmp_op f` by metis_tac[] >> simp[])
   >- (`no_tmp_op f'' <= no_tmp_op f` by metis_tac[] >> simp[])
   >- (`no_tmp_op f'' <= no_tmp_op f'` by metis_tac[] >> simp[])
   >- (`no_tmp_op f'' <= no_tmp_op f` by metis_tac[] >> simp[])
   >- (`no_tmp_op f'' <= no_tmp_op f'` by metis_tac[] >> simp[])
  );

val TMP_OP_EQ_LEMM = store_thm
  ("TMP_OP_EQ_LEMM",
   ``!f g. f ∈ subForms g ∧ (no_tmp_op f = no_tmp_op g) ==> (f = g)``,
   Induct_on `g` >> fs[] >> rpt strip_tac
   >> fs[subForms_def, no_tmp_op_def]
   >- (`no_tmp_op f <= no_tmp_op g` by metis_tac[TMP_OP_DECR_WITH_SF]
      >> `~(no_tmp_op g' >= 1)` by fs[] >> metis_tac[NO_TMP_LEMM])
   >- (`no_tmp_op f <= no_tmp_op g'` by metis_tac[TMP_OP_DECR_WITH_SF]
      >> `~(no_tmp_op g >= 1)` by fs[] >> metis_tac[NO_TMP_LEMM])
   >- (`no_tmp_op f <= no_tmp_op g` by metis_tac[TMP_OP_DECR_WITH_SF]
      >> `~(no_tmp_op g' >= 1)` by fs[] >> metis_tac[NO_TMP_LEMM])
   >- (`no_tmp_op f <= no_tmp_op g'` by metis_tac[TMP_OP_DECR_WITH_SF]
      >> `~(no_tmp_op g >= 1)` by fs[] >> metis_tac[NO_TMP_LEMM])
   >- (`no_tmp_op f <= no_tmp_op g` by metis_tac[TMP_OP_DECR_WITH_SF] >> fs[])
   >- (`no_tmp_op f <= no_tmp_op g` by metis_tac[TMP_OP_DECR_WITH_SF]
      >> fs[])
   >- (`no_tmp_op f <= no_tmp_op g'` by metis_tac[TMP_OP_DECR_WITH_SF]
                                    >> fs[])
   >- (`no_tmp_op f <= no_tmp_op g` by metis_tac[TMP_OP_DECR_WITH_SF]
                                    >> fs[])
   >- (`no_tmp_op f <= no_tmp_op g'` by metis_tac[TMP_OP_DECR_WITH_SF]
                                     >> fs[])
  );

val SF_ANTISYM_LEMM = store_thm
  ("SF_ANTISYM_LEMM",
   ``!f1 f2. (f1 ∈ subForms f2) /\ (f2 ∈ subForms f1) ==> (f1 = f2)``,
   Induct_on `f1` >> simp[subForms_def] >> rpt strip_tac >> simp[]
   >> `!f1 f2. (f1 ∈ subForms f2) ==> (no_tmp_op f1 <= no_tmp_op f2)`
        by metis_tac[TMP_OP_DECR_WITH_SF]
   >- (`no_tmp_op f2 <= no_tmp_op f1` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> `no_tmp_op (DISJ f1 f1') <= no_tmp_op f2` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> fs[no_tmp_op_def] >> `no_tmp_op f1' = 0` by simp[]
       >> `no_tmp_op f1' >= 1` by metis_tac[NO_TMP_LEMM] >> fs[]
      )
   >- (`no_tmp_op f2 <= no_tmp_op f1'` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> `no_tmp_op (DISJ f1 f1') <= no_tmp_op f2` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> fs[no_tmp_op_def] >> `no_tmp_op f1 = 0` by simp[]
       >> `no_tmp_op f1 >= 1` by metis_tac[NO_TMP_LEMM] >> fs[]
      )
   >- (`no_tmp_op f2 <= no_tmp_op f1` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> `no_tmp_op (CONJ f1 f1') <= no_tmp_op f2` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> fs[no_tmp_op_def] >> `no_tmp_op f1' = 0` by simp[]
       >> `no_tmp_op f1' >= 1` by metis_tac[NO_TMP_LEMM] >> fs[]
      )
   >- (`no_tmp_op f2 <= no_tmp_op f1'` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> `no_tmp_op (CONJ f1 f1') <= no_tmp_op f2` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> fs[no_tmp_op_def] >> `no_tmp_op f1 = 0` by simp[]
       >> `no_tmp_op f1 >= 1` by metis_tac[NO_TMP_LEMM] >> fs[]
      )
   >- (`no_tmp_op f2 <= no_tmp_op f1` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> `no_tmp_op (X f1) <= no_tmp_op f2` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> fs[no_tmp_op_def] >> `1 = 0` by simp[] >> fs[]
      )
   >- (`no_tmp_op f2 <= no_tmp_op f1` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> `no_tmp_op (U f1 f1') <= no_tmp_op f2` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> fs[no_tmp_op_def]
      )
   >- (`no_tmp_op f2 <= no_tmp_op f1'` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> `no_tmp_op (U f1 f1') <= no_tmp_op f2` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> fs[no_tmp_op_def]
      )
   >- (`no_tmp_op f2 <= no_tmp_op f1` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> `no_tmp_op (R f1 f1') <= no_tmp_op f2` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> fs[no_tmp_op_def]
      )
   >- (`no_tmp_op f2 <= no_tmp_op f1'` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> `no_tmp_op (R f1 f1') <= no_tmp_op f2` by metis_tac[TMP_OP_DECR_WITH_SF]
       >> fs[no_tmp_op_def]
      )
  );

val is_until_def = Define`
   (is_until (U f1 f2) = T)
 ∧ (is_until _ = F)`;

(*

  Temporal subformulae

*)


val tempSubForms_def = Define
   `(tempSubForms (VAR a) = {VAR a})
 /\ (tempSubForms (N_VAR a) = {N_VAR a})
 /\ (tempSubForms (DISJ f1 f2) = (tempSubForms f1) ∪ (tempSubForms f2))
 /\ (tempSubForms (CONJ f1 f2) = (tempSubForms f1) ∪ (tempSubForms f2))
 /\ (tempSubForms (X f) = {X f} ∪ (tempSubForms f))
 /\ (tempSubForms (U f1 f2) = {U f1 f2} ∪ (tempSubForms f1) ∪ (tempSubForms f2))
 /\ (tempSubForms (R f1 f2) = {R f1 f2} ∪ (tempSubForms f1) ∪ (tempSubForms f2))`;

val TSF_def = Define `
  TSF (x,y) = x ∈ tempSubForms y`;

val TSF_REFL = store_thm
  ("TSF_REFL",
   ``!f. reflexive (rrestrict TSF (tempSubForms f)) (tempSubForms f)``,
   fs[reflexive_def, rrestrict_def, TSF_def]
   >> Induct_on `f` >> fs[IN_DEF, TSF_def, tempSubForms_def] >> rpt strip_tac >> fs[]
   >- (`x ∈ tempSubForms x` suffices_by metis_tac[tempSubForms_def,IN_DEF]
      >> simp[tempSubForms_def] >> metis_tac[])
   >- (`!f1 f2. (U f1 f2) ∈ tempSubForms (U f1 f2)` by rw[tempSubForms_def]
       >> metis_tac[IN_DEF])
   >- (`!f1 f2. (R f1 f2) ∈ tempSubForms (R f1 f2)` by rw[tempSubForms_def]
       >> metis_tac[IN_DEF])
);

val TSF_SF_TRANS_LEMM = store_thm
  ("TSF_SF_TRANS_LEMM",
   ``!f1 f2 f3. f1 ∈ tempSubForms f2 /\ f2 ∈ subForms f3 ==> f1 ∈ tempSubForms f3``,
   Induct_on `f3` >> rpt strip_tac >> fs[tempSubForms_def, subForms_def]
   >> fs[tempSubForms_def] >> metis_tac[]
  );

val TSF_IMPL_SF = store_thm
  ("TSF_IMPL_SF",
   ``!f g. f ∈ tempSubForms g ==> f ∈ subForms g``,
   Induct_on `g` >> rpt strip_tac >> fs[tempSubForms_def, subForms_def]
  );

val TSF_TRANS_LEMM = store_thm
  ("TSF_TRANS_LEMM",
   ``transitive TSF``,
   simp[transitive_def,IN_DEF,TSF_def,tempSubForms_def]
   >> `!x y. tempSubForms x y = (y ∈ tempSubForms x)` by metis_tac[IN_DEF]
   >> Induct_on `z` >> dsimp[tempSubForms_def] >> metis_tac[]
  );

(* val TSF_TRANS_LEMM2 = store_thm *)
(*   ("TSF_TRANS_LEMM2", *)
(*    ``!x y z. (x,y) ∈ TSF ∧ (y,z) ∈ TSF ==> (x,z) ∈ TSF``, *)

(* ) *)


val TSF_TRANS = store_thm
  ("TSF_TRANS",
  ``!f. transitive (rrestrict TSF (tempSubForms f))``,
  metis_tac[RRESTRICT_TRANS, TSF_TRANS_LEMM]
  );

val TSF_FINITE = store_thm
  ("TSF_FINITE",
   ``!f. FINITE (tempSubForms f)``,
    Induct_on `f` >> fs[tempSubForms_def] >> strip_tac
  );

val TSF_ANTISYM_LEMM = store_thm
  ("TSF_ANTISYM_LEMM",
   ``!f1 f2. (f1 ∈ tempSubForms f2) /\ (f2 ∈ tempSubForms f1) ==> (f1 = f2)``,
   rpt strip_tac >> metis_tac[TSF_IMPL_SF, SF_ANTISYM_LEMM]
  );

val TSF_ANTISYM = store_thm
  ("TSF_ANTISYM",
   ``!f. antisym (rrestrict TSF (tempSubForms f))``,
   `antisym TSF` suffices_by metis_tac[RRESTRICT_ANTISYM]
   >> fs[TSF_def, antisym_def,IN_DEF] >> metis_tac[TSF_ANTISYM_LEMM,IN_DEF]
  );

val TSF_PO = store_thm
  ("TSF_PO",
  ``!f. partial_order (rrestrict TSF (tempSubForms f)) (tempSubForms f)``,
  fs[partial_order_def]
  >> rpt strip_tac
    >- (fs[domain_def, SUBSET_DEF, rrestrict_def] >> rpt strip_tac)
    >- (fs[range_def, SUBSET_DEF, rrestrict_def] >> rpt strip_tac)
    >- metis_tac[TSF_TRANS]
    >- metis_tac[TSF_REFL]
    >- metis_tac[TSF_ANTISYM]
  );

val STRICT_TSF_WF = store_thm
  ("STRICT_TSF_WF",
  ``WF (λf1 f2. f1 ∈ tempSubForms f2 ∧ ~(f1 = f2))``,
  rw[WF_IFF_WELLFOUNDED] >> simp[wellfounded_def] >> rpt strip_tac
  >> CCONTR_TAC >> fs[]
  >> `!n. no_tmp_op (f (SUC n)) < no_tmp_op (f n)` by (
      rpt strip_tac >> first_x_assum (qspec_then `n` mp_tac)
      >> rpt strip_tac
      >> imp_res_tac TSF_IMPL_SF
      >> imp_res_tac TMP_OP_DECR_WITH_SF
      >> Cases_on `(no_tmp_op (f (SUC n)) = no_tmp_op (f n))`
      >> fs[TMP_OP_EQ_LEMM]
  )
  >> `!n. (no_tmp_op o f) (SUC n) < (no_tmp_op o f) n` by fs[]
  >> `~wellfounded (\a b. (no_tmp_op o f) a < (no_tmp_op o f) b)` by (
      fs[wellfounded_def] >> metis_tac[]
  )
  >> `~wellfounded (inv_image ($<) (no_tmp_op o f))` by fs[inv_image_def]
  >> metis_tac[WF_LESS,WF_inv_image,WF_IFF_WELLFOUNDED]
  );

val DISJ_TEMP_SUBF = store_thm
  ("DISJ_TEMP_SUBF",
   ``!f f1 f2. ~(DISJ f1 f2 ∈ tempSubForms f)``,
   Induct_on `f` >> simp[tempSubForms_def]);

val CONJ_TEMP_SUBF = store_thm
  ("CONJ_TEMP_SUBF",
   ``!f f1 f2. ~(CONJ f1 f2 ∈ tempSubForms f)``,
    Induct_on `f` >> simp[tempSubForms_def]);


(*

 Temporal DNF

*)

val tempDNF_def = Define
   `(tempDNF (VAR a) = {{VAR a}})
 /\ (tempDNF (N_VAR a) = {{N_VAR a}})
 /\ (tempDNF (DISJ f1 f2) = (tempDNF f1) ∪ (tempDNF f2))
 /\ (tempDNF (CONJ f1 f2) = {f' ∪ f'' | (f' ∈ tempDNF f1) /\ (f'' ∈ tempDNF f2)})
 /\ (tempDNF (X f) = {{X f}})
 /\ (tempDNF (U f1 f2) = {{U f1 f2}})
 /\ (tempDNF (R f1 f2) = {{R f1 f2}})`;

val TEMPDNF_NOT_EMPTY = store_thm
  ("TEMPDNF_NOT_EMPTY",
   ``!f qs. qs ∈ tempDNF f ==> ~(qs = {})``,
   Induct_on `f` >> fs[tempDNF_def]
  );

val TEMPDNF_TEMPSUBF = store_thm
  ("TEMPDNF_TEMPSUBF",
   ``!f s. (s ∈ tempDNF f) ==> (s ⊆ tempSubForms f)``,
   Induct_on `f` >> simp[tempSubForms_def, tempDNF_def]
   >- (strip_tac >> ASM_CASES_TAC ``s ∈ tempDNF f`` >> simp[]
       >- (`tempSubForms f ⊆ tempSubForms f ∪ tempSubForms f'`
            by metis_tac[SUBSET_UNION]
           >> `s ⊆ tempSubForms f` suffices_by metis_tac[SUBSET_TRANS]
           >> simp[])
       >- (`tempSubForms f' ⊆ tempSubForms f ∪ tempSubForms f'`
               by metis_tac[SUBSET_UNION]
           >> strip_tac
           >> `s ⊆ tempSubForms f'` suffices_by metis_tac[SUBSET_TRANS]
           >> simp[]))
   >- (rpt strip_tac
       >> `f'' ⊆ tempSubForms f` by metis_tac[]
       >> `f''' ⊆ tempSubForms f'` by metis_tac[]
       >> fs[SUBSET_DEF]
       >> rpt strip_tac >> metis_tac[])
  );

(*
  LTL language
*)

val props_def = Define
`props f = {a | (VAR a) ∈ (subForms f) \/ (N_VAR a) ∈ (subForms f) }`;

val ltl_lang_def = Define
`ltl_lang f = {w | MODELS w f /\ word_range w ⊆ POW (props f)}`;

(*
   EXAMPLES
*)

val W1_def = Define `W1 = WORD (\x. {x})`;

val EX1 = store_thm
 ("EX1", ``(MODELS W1 TRUE)``,  fs[MODELS_def,TRUE_def]);

val EX2 = store_thm
 ("EX2", ``MODELS W1 (VAR 0)``, simp[MODELS_def, at_def, W1_def]);

val EX3 = store_thm
 ("EX3",``MODELS W1 (U TRUE (VAR 23))``,
  simp [MODELS_def, TRUE_def, suff_def, at_def, W1_def]);

val EX4 = store_thm
  ("EX4",``!x. ?y. MODELS (suff W1 x) (U (VAR x) (VAR y))``,
   simp [MODELS_def, suff_def, at_def, W1_def] >> rpt strip_tac
     >> exists_tac ``0`` >> simp[]
  );

(* Full LTL *)

val _ = Datatype`
  full_ltl_frml
  = F_VAR 'a
  | F_CONJ full_ltl_frml full_ltl_frml
  | F_NEG full_ltl_frml
  | F_X full_ltl_frml
  | F_U full_ltl_frml full_ltl_frml`;

val FLTL_MODELS_def =
    Define
      `(FLTL_MODELS w (F_VAR a) = (a ∈ (at w 0)))
    /\ (FLTL_MODELS w (F_CONJ f1 f2) = (FLTL_MODELS w f1) /\ (FLTL_MODELS w f2))
    /\ (FLTL_MODELS w (F_NEG f) = ~(FLTL_MODELS w f))
    /\ (FLTL_MODELS w (F_X f) = (FLTL_MODELS (suff w 1) f))
    /\ (FLTL_MODELS w (F_U f1 f2) =
        ?n. (FLTL_MODELS (suff w n) f2) /\ !i. (i < n) ==> (FLTL_MODELS (suff w i) f1))`;

val NNF_def = Define`
    (NNF (F_VAR a) = VAR a)
  ∧ (NNF (F_CONJ f1 f2) = CONJ (NNF f1) (NNF f2))
  ∧ (NNF (F_NEG (F_VAR a)) = N_VAR a)
  ∧ (NNF (F_NEG (F_CONJ f1 f2)) = DISJ (NNF (F_NEG f1)) (NNF (F_NEG f2)))
  ∧ (NNF (F_NEG (F_NEG f)) =  NNF f)
  ∧ (NNF (F_NEG (F_X f)) = X (NNF (F_NEG f)))
  ∧ (NNF (F_NEG (F_U f1 f2)) = R (NNF (F_NEG f1)) (NNF (F_NEG f2)))
  ∧ (NNF (F_X f) = X (NNF f))
  ∧ (NNF (F_U f1 f2) = U (NNF f1) (NNF f2))`;

val NNF_NEG_LEMM = store_thm
  ("NNF_NEG_LEMM",
   ``!f w. MODELS w (NNF (F_NEG f)) = ~MODELS w (NNF f)``,
   Induct_on `f` >> fs[MODELS_def, NNF_def]
  );

val NNF_THM = store_thm
  ("NNF_THM",
   ``!f w. FLTL_MODELS w f = MODELS w (NNF f)``,
   Induct_on `f` >> fs[FLTL_MODELS_def, MODELS_def, NNF_def]
   >> metis_tac[NNF_NEG_LEMM]
  );

val LTL_FALSE_def = zDefine `
  LTL_FALSE p  = F_CONJ (F_VAR p) (F_NEG (F_VAR p))`;

val LTL_TRUE_def = zDefine `
  LTL_TRUE p = F_NEG (LTL_FALSE p)`;

val LTL_F_def = zDefine `
  LTL_F φ p = F_U (LTL_TRUE p) φ`

val LTL_G_def = zDefine `
  LTL_G φ p = F_NEG (LTL_F (F_NEG φ) p)`;

(* Some example formulae*)

val LTL_EX1_def = Define`
 LTL_EX1 = VAR 0`;

val LTL_EX2_def = Define`
 LTL_EX2 = U (VAR 0) (VAR 1)`;

val LTL_EX3_def = Define`
 LTL_EX3 = R (VAR 0) (VAR 1)`;

val LTL_EX4_def = Define`
 LTL_EX4 = NNF (F_CONJ (LTL_G (LTL_F (F_VAR 1) 0) 0)
                       ((LTL_F (F_CONJ (F_VAR 2) (LTL_G (F_NEG (F_VAR 3)) 0)) 0)))`;

val LTL_EX5_def = Define`
 LTL_EX5 = NNF (F_CONJ (F_CONJ (LTL_G (LTL_F (F_VAR 1) 0) 0)
                               (LTL_G (LTL_F (F_VAR 2) 0) 0)
                       )
                       ((LTL_F (F_CONJ (F_VAR 3) (LTL_G (F_NEG (F_VAR 4)) 0)) 0)))`;

Definition LTL_EX6_def:
  LTL_EX6 = NNF (F_CONJ (F_CONJ (F_CONJ (LTL_G (LTL_F (F_VAR 1) 0) 0)
                                        (LTL_G (LTL_F (F_VAR 2) 0) 0)
                                )
                                (LTL_G (LTL_F (F_VAR 3) 0) 0)
                        )
                        ((LTL_F (F_CONJ (F_VAR 4) (LTL_G (F_NEG (F_VAR 5)) 0)
                                )
                                0)))
End

val _ = export_theory();
