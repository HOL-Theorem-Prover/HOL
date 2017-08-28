open HolKernel Parse boolLib bossLib pred_setTheory relationTheory set_relationTheory

open generalHelpersTheory wordTheory

val _ = new_theory "ltl"

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

val EX_1 = store_thm
 ("EX1", ``(MODELS W1 TRUE)``,  fs[MODELS_def,TRUE_def]);

val EX_2 = store_thm
 ("EX2", ``MODELS W1 (VAR 0)``, simp[MODELS_def, at_def, W1_def]);

val EX_3 = store_thm
 ("EX3",``MODELS W1 (U TRUE (VAR 23))``,
  simp [MODELS_def, TRUE_def, suff_def, at_def, W1_def]);

val EX_4 = store_thm
  ("EX4",``!x. ?y. MODELS (suff W1 x) (U (VAR x) (VAR y))``,
   simp [MODELS_def, suff_def, at_def, W1_def] >> rpt strip_tac
     >> exists_tac ``0`` >> simp[]
  );

val _ = export_theory();
