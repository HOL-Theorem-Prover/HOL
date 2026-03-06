Theory ltl
Ancestors
  pred_set relation set_relation prim_rec generalHelpers word

val _ = ParseExtras.temp_loose_equality()

Datatype:
  ltl_frml
  = VAR 'a
  | N_VAR 'a
  | DISJ ltl_frml ltl_frml
  | CONJ ltl_frml ltl_frml
  | X ltl_frml
  | U ltl_frml ltl_frml
  | R ltl_frml ltl_frml
End

Definition MODELS_def:
     (MODELS w (VAR a) = (a IN (at w 0)))
  /\ (MODELS w (N_VAR a) = ~(a IN (at w 0)))
  /\ (MODELS w (DISJ f1 f2) = (MODELS w f1) \/ (MODELS w f2))
  /\ (MODELS w (CONJ f1 f2) = (MODELS w f1) /\ (MODELS w f2))
  /\ (MODELS w (X f) = (MODELS (suff w 1) f))
  /\ (MODELS w (U f1 f2) =
        ?n. (MODELS (suff w n) f2) /\ !i. (i < n) ==> (MODELS (suff w i) f1))
  /\ (MODELS w (R f1 f2) =
        !n. (MODELS (suff w n) f2) \/ ?i. (i < n) /\ (MODELS (suff w i) f1))
End

Theorem R_COND_LEMM:
     !w f1 f2. (!n. (MODELS (suff w n) f2) \/ ?i. (i < n) /\ (MODELS (suff w i) f1))
      = ((!n. MODELS (suff w n) f2) \/
         ?n. MODELS (suff w n) f1 /\ !i. i <= n ==> MODELS (suff w i) f2)
Proof
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
QED

Definition TRUE_def:   TRUE = DISJ (VAR ARB) (N_VAR ARB)
End
Definition FALSE_def:   FALSE = CONJ (VAR ARB) (N_VAR ARB)
End

(*

  Subformulae

*)

Definition subForms_def:
       (subForms (VAR a) = {VAR a})
    /\ (subForms (N_VAR a) = {N_VAR a})
    /\ (subForms (DISJ f1 f2) = {DISJ f1 f2} ∪ (subForms f1) ∪ (subForms f2))
    /\ (subForms (CONJ f1 f2) = {CONJ f1 f2} ∪ (subForms f1) ∪ (subForms f2))
    /\ (subForms (X f) = {X f} ∪ (subForms f))
    /\ (subForms (U f1 f2) = {U f1 f2} ∪ (subForms f1) ∪ (subForms f2))
    /\ (subForms (R f1 f2) = {R f1 f2} ∪ (subForms f1) ∪ (subForms f2))
End

Theorem SUBFORMS_REFL:
     !f. f ∈ subForms f
Proof
   Induct_on `f` >> simp[subForms_def]
QED

Theorem SUBFORMS_TRANS:
    !f1 f2 f3. f1 ∈ subForms f2 /\ f2 ∈ subForms f3 ==> f1 ∈ subForms f3
Proof
  Induct_on `f3` >> rpt strip_tac >> dsimp[] >> fs[subForms_def, UNION_DEF]
  >> fs[subForms_def, UNION_DEF]
  >> metis_tac[]
QED

Definition no_tmp_op_def:
 (no_tmp_op (VAR a) = 1)
    /\ (no_tmp_op (N_VAR a) = 1)
    /\ (no_tmp_op (DISJ f1 f2) = (no_tmp_op f1) + (no_tmp_op f2))
    /\ (no_tmp_op (CONJ f1 f2) = (no_tmp_op f1) + (no_tmp_op f2))
    /\ (no_tmp_op (X f) = (no_tmp_op f) + 1)
    /\ (no_tmp_op (U f1 f2) =(no_tmp_op f1) + (no_tmp_op f2) +1)
    /\ (no_tmp_op (R f1 f2) =(no_tmp_op f1) + (no_tmp_op f2) +1)
End

Theorem NO_TMP_LEMM:   !f. no_tmp_op f >= 1
Proof
    Induct_on `f` >> simp[no_tmp_op_def]
QED

Theorem TMP_OP_DECR_WITH_SF:
     !f f'. (f' ∈ subForms f ==> (no_tmp_op f' <= no_tmp_op f))
Proof
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
QED

Theorem TMP_OP_EQ_LEMM:
     !f g. f ∈ subForms g ∧ (no_tmp_op f = no_tmp_op g) ==> (f = g)
Proof
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
QED

Theorem SF_ANTISYM_LEMM:
     !f1 f2. (f1 ∈ subForms f2) /\ (f2 ∈ subForms f1) ==> (f1 = f2)
Proof
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
QED

Definition is_until_def:
   (is_until (U f1 f2) = T)
 ∧ (is_until _ = F)
End

(*

  Temporal subformulae

*)


Definition tempSubForms_def:
    (tempSubForms (VAR a) = {VAR a})
 /\ (tempSubForms (N_VAR a) = {N_VAR a})
 /\ (tempSubForms (DISJ f1 f2) = (tempSubForms f1) ∪ (tempSubForms f2))
 /\ (tempSubForms (CONJ f1 f2) = (tempSubForms f1) ∪ (tempSubForms f2))
 /\ (tempSubForms (X f) = {X f} ∪ (tempSubForms f))
 /\ (tempSubForms (U f1 f2) = {U f1 f2} ∪ (tempSubForms f1) ∪ (tempSubForms f2))
 /\ (tempSubForms (R f1 f2) = {R f1 f2} ∪ (tempSubForms f1) ∪ (tempSubForms f2))
End

Definition TSF_def:
  TSF (x,y) = x ∈ tempSubForms y
End

Theorem TSF_REFL:
     !f. reflexive (rrestrict TSF (tempSubForms f)) (tempSubForms f)
Proof
   fs[reflexive_def, rrestrict_def, TSF_def]
   >> Induct_on `f` >> fs[IN_DEF, TSF_def, tempSubForms_def] >> rpt strip_tac >> fs[]
   >- (`x ∈ tempSubForms x` suffices_by metis_tac[tempSubForms_def,IN_DEF]
      >> simp[tempSubForms_def] >> metis_tac[])
   >- (`!f1 f2. (U f1 f2) ∈ tempSubForms (U f1 f2)` by rw[tempSubForms_def]
       >> metis_tac[IN_DEF])
   >- (`!f1 f2. (R f1 f2) ∈ tempSubForms (R f1 f2)` by rw[tempSubForms_def]
       >> metis_tac[IN_DEF])
QED

Theorem TSF_SF_TRANS_LEMM:
     !f1 f2 f3. f1 ∈ tempSubForms f2 /\ f2 ∈ subForms f3 ==> f1 ∈ tempSubForms f3
Proof
   Induct_on `f3` >> rpt strip_tac >> fs[tempSubForms_def, subForms_def]
   >> fs[tempSubForms_def] >> metis_tac[]
QED

Theorem TSF_IMPL_SF:
     !f g. f ∈ tempSubForms g ==> f ∈ subForms g
Proof
   Induct_on `g` >> rpt strip_tac >> fs[tempSubForms_def, subForms_def]
QED

Theorem TSF_TRANS_LEMM:
     transitive TSF
Proof
   simp[transitive_def,IN_DEF,TSF_def,tempSubForms_def]
   >> `!x y. tempSubForms x y = (y ∈ tempSubForms x)` by metis_tac[IN_DEF]
   >> Induct_on `z` >> dsimp[tempSubForms_def] >> metis_tac[]
QED

(* val TSF_TRANS_LEMM2 = store_thm *)
(*   ("TSF_TRANS_LEMM2", *)
(*    ``!x y z. (x,y) ∈ TSF ∧ (y,z) ∈ TSF ==> (x,z) ∈ TSF``, *)

(* ) *)


Theorem TSF_TRANS:
    !f. transitive (rrestrict TSF (tempSubForms f))
Proof
  metis_tac[RRESTRICT_TRANS, TSF_TRANS_LEMM]
QED

Theorem TSF_FINITE:
     !f. FINITE (tempSubForms f)
Proof
    Induct_on `f` >> fs[tempSubForms_def] >> strip_tac
QED

Theorem TSF_ANTISYM_LEMM:
     !f1 f2. (f1 ∈ tempSubForms f2) /\ (f2 ∈ tempSubForms f1) ==> (f1 = f2)
Proof
   rpt strip_tac >> metis_tac[TSF_IMPL_SF, SF_ANTISYM_LEMM]
QED

Theorem TSF_ANTISYM:
     !f. antisym (rrestrict TSF (tempSubForms f))
Proof
   `antisym TSF` suffices_by metis_tac[RRESTRICT_ANTISYM]
   >> fs[TSF_def, antisym_def,IN_DEF] >> metis_tac[TSF_ANTISYM_LEMM,IN_DEF]
QED

Theorem TSF_PO:
    !f. partial_order (rrestrict TSF (tempSubForms f)) (tempSubForms f)
Proof
  fs[partial_order_def]
  >> rpt strip_tac
    >- (fs[domain_def, SUBSET_DEF, rrestrict_def] >> rpt strip_tac)
    >- (fs[range_def, SUBSET_DEF, rrestrict_def] >> rpt strip_tac)
    >- metis_tac[TSF_TRANS]
    >- metis_tac[TSF_REFL]
    >- metis_tac[TSF_ANTISYM]
QED

Theorem STRICT_TSF_WF:
    WF (λf1 f2. f1 ∈ tempSubForms f2 ∧ ~(f1 = f2))
Proof
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
QED

Theorem DISJ_TEMP_SUBF:
     !f f1 f2. ~(DISJ f1 f2 ∈ tempSubForms f)
Proof
   Induct_on `f` >> simp[tempSubForms_def]
QED

Theorem CONJ_TEMP_SUBF:
     !f f1 f2. ~(CONJ f1 f2 ∈ tempSubForms f)
Proof
    Induct_on `f` >> simp[tempSubForms_def]
QED


(*

 Temporal DNF

*)

Definition tempDNF_def:
    (tempDNF (VAR a) = {{VAR a}})
 /\ (tempDNF (N_VAR a) = {{N_VAR a}})
 /\ (tempDNF (DISJ f1 f2) = (tempDNF f1) ∪ (tempDNF f2))
 /\ (tempDNF (CONJ f1 f2) = {f' ∪ f'' | (f' ∈ tempDNF f1) /\ (f'' ∈ tempDNF f2)})
 /\ (tempDNF (X f) = {{X f}})
 /\ (tempDNF (U f1 f2) = {{U f1 f2}})
 /\ (tempDNF (R f1 f2) = {{R f1 f2}})
End

Theorem TEMPDNF_NOT_EMPTY:
     !f qs. qs ∈ tempDNF f ==> ~(qs = {})
Proof
   Induct_on `f` >> fs[tempDNF_def]
QED

Theorem TEMPDNF_TEMPSUBF:
     !f s. (s ∈ tempDNF f) ==> (s ⊆ tempSubForms f)
Proof
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
QED

(*
  LTL language
*)

Definition props_def:
 props f = {a | (VAR a) ∈ (subForms f) \/ (N_VAR a) ∈ (subForms f) }
End

Definition ltl_lang_def:
 ltl_lang f = {w | MODELS w f /\ word_range w ⊆ POW (props f)}
End

(*
   EXAMPLES
*)

Definition W1_def:   W1 = WORD (\x. {x})
End

Theorem EX1:   (MODELS W1 TRUE)
Proof  fs[MODELS_def,TRUE_def]
QED

Theorem EX2:   MODELS W1 (VAR 0)
Proof simp[MODELS_def, at_def, W1_def]
QED

Theorem EX3:  MODELS W1 (U TRUE (VAR 23))
Proof
  simp [MODELS_def, TRUE_def, suff_def, at_def, W1_def]
QED

Theorem EX4:  !x. ?y. MODELS (suff W1 x) (U (VAR x) (VAR y))
Proof
   simp [MODELS_def, suff_def, at_def, W1_def] >> rpt strip_tac
     >> exists_tac ``0`` >> simp[]
QED

(* Full LTL *)

Datatype:
  full_ltl_frml
  = F_VAR 'a
  | F_CONJ full_ltl_frml full_ltl_frml
  | F_NEG full_ltl_frml
  | F_X full_ltl_frml
  | F_U full_ltl_frml full_ltl_frml
End

Definition FLTL_MODELS_def:
       (FLTL_MODELS w (F_VAR a) = (a ∈ (at w 0)))
    /\ (FLTL_MODELS w (F_CONJ f1 f2) = (FLTL_MODELS w f1) /\ (FLTL_MODELS w f2))
    /\ (FLTL_MODELS w (F_NEG f) = ~(FLTL_MODELS w f))
    /\ (FLTL_MODELS w (F_X f) = (FLTL_MODELS (suff w 1) f))
    /\ (FLTL_MODELS w (F_U f1 f2) =
        ?n. (FLTL_MODELS (suff w n) f2) /\ !i. (i < n) ==> (FLTL_MODELS (suff w i) f1))
End

Definition NNF_def:
    (NNF (F_VAR a) = VAR a)
  ∧ (NNF (F_CONJ f1 f2) = CONJ (NNF f1) (NNF f2))
  ∧ (NNF (F_NEG (F_VAR a)) = N_VAR a)
  ∧ (NNF (F_NEG (F_CONJ f1 f2)) = DISJ (NNF (F_NEG f1)) (NNF (F_NEG f2)))
  ∧ (NNF (F_NEG (F_NEG f)) =  NNF f)
  ∧ (NNF (F_NEG (F_X f)) = X (NNF (F_NEG f)))
  ∧ (NNF (F_NEG (F_U f1 f2)) = R (NNF (F_NEG f1)) (NNF (F_NEG f2)))
  ∧ (NNF (F_X f) = X (NNF f))
  ∧ (NNF (F_U f1 f2) = U (NNF f1) (NNF f2))
End

Theorem NNF_NEG_LEMM:
     !f w. MODELS w (NNF (F_NEG f)) = ~MODELS w (NNF f)
Proof
   Induct_on `f` >> fs[MODELS_def, NNF_def]
QED

Theorem NNF_THM:
     !f w. FLTL_MODELS w f = MODELS w (NNF f)
Proof
   Induct_on `f` >> fs[FLTL_MODELS_def, MODELS_def, NNF_def]
   >> metis_tac[NNF_NEG_LEMM]
QED

Definition LTL_FALSE_def[nocompute]:
  LTL_FALSE p  = F_CONJ (F_VAR p) (F_NEG (F_VAR p))
End

Definition LTL_TRUE_def[nocompute]:
  LTL_TRUE p = F_NEG (LTL_FALSE p)
End

Definition LTL_F_def[nocompute]:
  LTL_F φ p = F_U (LTL_TRUE p) φ
End

Definition LTL_G_def[nocompute]:
  LTL_G φ p = F_NEG (LTL_F (F_NEG φ) p)
End

(* Some example formulae*)

Definition LTL_EX1_def:
 LTL_EX1 = VAR 0
End

Definition LTL_EX2_def:
 LTL_EX2 = U (VAR 0) (VAR 1)
End

Definition LTL_EX3_def:
 LTL_EX3 = R (VAR 0) (VAR 1)
End

Definition LTL_EX4_def:
 LTL_EX4 = NNF (F_CONJ (LTL_G (LTL_F (F_VAR 1) 0) 0)
                       ((LTL_F (F_CONJ (F_VAR 2) (LTL_G (F_NEG (F_VAR 3)) 0)) 0)))
End

Definition LTL_EX5_def:
 LTL_EX5 = NNF (F_CONJ (F_CONJ (LTL_G (LTL_F (F_VAR 1) 0) 0)
                               (LTL_G (LTL_F (F_VAR 2) 0) 0)
                       )
                       ((LTL_F (F_CONJ (F_VAR 3) (LTL_G (F_NEG (F_VAR 4)) 0)) 0)))
End

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

