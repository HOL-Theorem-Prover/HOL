open HolKernel Parse bossLib boolLib pairTheory relationTheory set_relationTheory pred_setTheory arithmeticTheory

open wordTheory buechiATheory alterATheory generalHelpersTheory

val _ = new_theory "waa2ba"

val d_gen_def = Define`
  d_gen (waa : (α,β) ALTER_A) qs
  = (d_conj_set { (q, waa.trans q) | q ∈ qs } (waa.alphabet))`;

val tr_less_general_def = Define`
  tr_less_general AccSet qs =
   { ((a1,e1),(a2,e2)) |
             (a2 ⊆ a1) ∧ (e1 ⊆ e2)
           ∧ (!T'. (T' ∈ AccSet)
                   ==> (((qs,a2,e2) ∈ T') ==> (qs,a1,e1) ∈ T'))}`;

val TLG_PO = store_thm
  ("TLG_PO",
  ``!d AccS q. partial_order (rrestrict (tr_less_general AccS q) d) d``,
  fs[rrestrict_def, partial_order_def, tr_less_general_def]
  >> rpt strip_tac
    >- (fs[domain_def, SUBSET_DEF] >> rpt strip_tac)
    >- (fs[range_def, SUBSET_DEF] >> rpt strip_tac)
    >- (fs[transitive_def] >> rpt strip_tac >> rw[]
        >> metis_tac[SUBSET_TRANS])
    >- (fs[reflexive_def] >> rpt strip_tac
          >> Cases_on `x` >> metis_tac[SUBSET_REFL])
    >- (fs[antisym_def] >> rpt strip_tac >> rw[] >> metis_tac[SUBSET_ANTISYM])
  );

val acc_cond_def = Define`
acc_cond waa f =
  { (e,a,e')
  | e ∈ (POW waa.states)
      ∧ e' ∈ (POW waa.states)
      ∧ a ∈ (POW waa.alphabet)
      ∧ (~(f ∈ e') \/
         (?b e''. ((b, e'') ∈ waa.trans f) ∧ a ⊆ b
           ∧ ~(f ∈ e'') ∧ e'' ⊆ e')) }`;

val all_acc_cond_def = Define`
  all_acc_cond (waa : (β, α) ALTER_A)  =
  { acc_cond waa f | f | f ∈ waa.final}`;

val gba_trans_def = Define`
gba_trans (waa : (α,β) ALTER_A) qs =
  { (a,e')
  | (a,e') ∈
           minimal_elements
           (d_gen waa qs)
           (rrestrict (tr_less_general (all_acc_cond waa) qs) (d_gen waa qs))}`;

val gba_accTrans_def = Define`
gba_accTrans (waa : (β, α) ALTER_A)  =
  let realTransitions =
       { (e,a,e') | (a,e') ∈ (gba_trans waa e) ∧ e ∈ POW waa.states }
  in { acc_cond waa f ∩ realTransitions | f | f ∈ waa.final}`;

val vwaa2gba_def = Define`
vwaa2gba waa =
     if isVeryWeakAlterA waa
     then GBA
              (POW waa.states)
              waa.initial
              (gba_trans waa)
              (gba_accTrans waa)
              waa.alphabet
     else ARB`;

val ITSET_IND_SPEC = store_thm
  ("ITSET_IND_SPEC",
   ``∀P.
    (∀s b. (FINITE s ∧ s ≠ ∅ ⇒ P (REST s) ((d_conj o SND) (CHOICE s) b)) ⇒ P s b) ⇒
     ∀v v1. P v v1``, metis_tac[ITSET_IND]
  );

val D_GEN_FINITE = store_thm
  ("D_GEN_FINITE",
   ``!waa qs. FINITE waa.alphabet ∧ FINITE waa.states ∧ qs ⊆ waa.states
  ∧ isValidAlterA waa
  ==> finite_prefixes
  (rrestrict (tr_less_general (all_acc_cond waa) qs) (d_gen waa qs))
  (d_gen waa qs)``,
   rpt strip_tac
   >> `FINITE qs` by metis_tac[PSUBSET_DEF, PSUBSET_FINITE]
   >> fs[finite_prefixes_def, rrestrict_def,d_gen_def] >> rpt strip_tac
   >> `FINITE {e' | e' ∈ { e' | (e', e) ∈ tr_less_general (all_acc_cond waa) qs}
                       ∧ e' ∈ d_conj_set {(q, waa.trans q) | q ∈ qs} waa.alphabet}`
      suffices_by (rpt strip_tac >> fs[])
   >> `FINITE (d_conj_set { (q, waa.trans q) | q ∈ qs } waa.alphabet)`
      suffices_by metis_tac[FINITE_INTER, INTER_DEF]
   >> simp[d_conj_set_def, d_conj_def]
   >> `!v v1. FINITE v1 ∧ FINITE v
  ∧ (!v' q. (q:β, v':((α set) # (β set)) set) ∈ v ==> FINITE v')
                     ==> FINITE (ITSET (d_conj o SND) v v1)` by (
       HO_MATCH_MP_TAC ITSET_IND_SPEC
       >> rpt strip_tac >> Cases_on `v = {}`
         >- (`ITSET (d_conj o SND) v v1 = v1` by metis_tac[ITSET_def] >> fs[])
         >- (fs[]
             >> `!v' q. (q, v') ∈ REST v ==> FINITE v'`
                by (fs[REST_DEF, DELETE_DEF, DIFF_DEF] >> rpt strip_tac >> metis_tac[])
             >> `FINITE (d_conj (SND (CHOICE v)) v1)` by (
                  `FINITE (SND (CHOICE v))`
                       by (Cases_on `CHOICE v` >> metis_tac[CHOICE_DEF,SND])
                  >> metis_tac[D_CONJ_FINITE]
              )
             >> fs[]
             >> `FINITE (ITSET (d_conj ∘ SND) (REST v) (d_conj (SND (CHOICE v)) v1))`
                 by metis_tac[]
             >> `FINITE (ITSET (d_conj ∘ SND) (REST v) ((d_conj o SND) (CHOICE v) v1))`
                 by fs[]
             >> metis_tac[ITSET_def]
            )
   )
   >> first_x_assum (qspec_then `{(q,waa.trans q) | q ∈ qs}` mp_tac)
   >> rpt strip_tac >> first_x_assum (qspec_then `{(waa.alphabet,∅)}` mp_tac)
   >> rpt strip_tac >> fs[SING_FINITE]
   >> `FINITE {(q, waa.trans q) | q ∈ qs}` by metis_tac[IMAGE_FINITE,IMAGE_DEF]
   >> fs[]
   >> `(∀v'. (∃q. (v' = waa.trans q) ∧ q ∈ qs) ⇒ FINITE v')` by (
       rpt strip_tac >> fs[isValidAlterA_def]
       >> `waa.trans q ⊆ {(a,e) | a ∈ POW waa.alphabet ∧ e ∈ POW waa.states }` by (
           simp[SUBSET_DEF] >> rpt strip_tac >> Cases_on `x`
           >> metis_tac[SUBSET_DEF,IN_POW]
       )
       >> `FINITE (POW waa.alphabet × POW waa.states)`
                by metis_tac[FINITE_CROSS,FINITE_POW]
       >> `{(a,e) | a ∈ POW waa.alphabet ∧ e ∈ POW waa.states} =
                 POW waa.alphabet × POW waa.states` by (
               simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
               >> fs[FST,SND] >> qexists_tac `FST x` >> qexists_tac `SND x`
               >> fs[FST,SND]
       )
       >> metis_tac[PSUBSET_DEF, PSUBSET_FINITE]
   )
   >> `(∀q. q ∈ qs ⇒ FINITE (waa.trans q))` by metis_tac[]
   >> fs[]
  );

val D_GEN_HAS_MIN = store_thm
  ("D_GEN_HAS_MIN",
   ``!waa qs a e. FINITE waa.alphabet ∧ FINITE waa.states ∧ qs ⊆ waa.states
     ∧ isValidAlterA waa ∧ (a,e) ∈ (d_gen waa qs)
     ==> ?a' e'. (a',e') ∈
     minimal_elements
     (d_gen waa qs) (rrestrict (tr_less_general (all_acc_cond waa) qs) (d_gen waa qs))
     ∧ ((a',e'), (a,e)) ∈ tr_less_general (all_acc_cond waa) qs``,
   rpt strip_tac >> imp_res_tac D_GEN_FINITE
   >> `partial_order (rrestrict (tr_less_general (all_acc_cond waa) qs) (d_gen waa qs))
     (d_gen waa qs)`
      by fs[TLG_PO]
   >> Cases_on `(a,e) ∈
     minimal_elements (d_gen waa qs) (rrestrict (tr_less_general (all_acc_cond waa) qs)
                                                (d_gen waa qs))`
    >- (qexists_tac `a` >> qexists_tac `e`
        >> fs[tr_less_general_def])
    >- (`∃x'. x' ∈
       minimal_elements (d_gen waa qs) (rrestrict (tr_less_general (all_acc_cond waa) qs)
                                                  (d_gen waa qs))
       ∧ (x', a, e) ∈ (rrestrict (tr_less_general (all_acc_cond waa) qs) (d_gen waa qs))`
       by metis_tac[finite_prefix_po_has_minimal_path,SUBSET_REFL]
       >> Cases_on `x'` >> qexists_tac `q` >> qexists_tac `r`
       >> fs[tr_less_general_def, rrestrict_def]
       )
  );

val D_GEN_A_E_LEMM = store_thm
  ("D_GEN_A_E_LEMM",
   ``!qs aut a e. FINITE qs ∧ ((a,e) ∈ d_gen aut qs)
     ==> (!q. q ∈ qs ==> ?a' e'. (a',e') ∈ aut.trans q ∧ a ⊆ a' ∧ e' ⊆ e)``,
   rpt gen_tac >> strip_tac >> fs[d_gen_def]
   >> `!q d. (q,d) ∈ {(q, aut.trans q) | q ∈ qs}
       ==> ∃a' e'. (a',e') ∈ d ∧ a ⊆ a' ∧ e' ⊆ e` suffices_by (
       rpt strip_tac
       >> `(q,aut.trans q) ∈ {(q, aut.trans q) | q ∈ qs }` by fs[]
       >> metis_tac[]
   )
   >> `FINITE {(q,aut.trans q) | q ∈ qs }` by metis_tac[IMAGE_FINITE, IMAGE_DEF]
   >> HO_MATCH_MP_TAC D_CONJ_SET_LEMM2
   >> metis_tac[]
  );

val D_GEN_A_E_LEMM2 = store_thm
  ("D_GEN_A_E_LEMM2",
   ``!qs aut a e a' e'. FINITE qs
        ∧ (!q. q ∈ qs ==> (a' q,e' q) ∈ (aut.trans q) ∧ a ⊆ a' q ∧ e' q ⊆ e)
        ∧ a ⊆ aut.alphabet
 ==> (aut.alphabet ∩ BIGINTER {a' q | q ∈ qs }, BIGUNION {e' q | q ∈ qs})
                      ∈ d_gen aut qs``,
   rpt strip_tac >> fs[d_gen_def]
   >> qabbrev_tac `s = {(q,aut.trans q) | q ∈ qs}`
   >> `!q. q ∈ qs = q ∈ IMAGE FST s` by (
       simp[EQ_IMP_THM] >> rpt strip_tac
       >- (qexists_tac `(q, aut.trans q)` >> qunabbrev_tac `s` >> fs[])
       >- (qunabbrev_tac `s` >> Cases_on `x` >> fs[])
   )
   >> rw[]
   >> `(aut.alphabet ∩ BIGINTER {a' q | q ∈ IMAGE FST s},
       BIGUNION {e' q | q ∈ IMAGE FST s}) ∈ d_conj_set s aut.alphabet`
       by (HO_MATCH_MP_TAC D_CONJ_SET_LEMM3
           >> `FINITE s` by (
                `s = IMAGE (λq. (q,aut.trans q)) qs` by (
                    qunabbrev_tac `s` >> simp[SET_EQ_SUBSET,SUBSET_DEF]
                )
                >> metis_tac[IMAGE_FINITE]
            )
           >> qexists_tac `a` >> fs[] >> qunabbrev_tac `s` >> fs[]
          )
   >> fs[IN_IMAGE]
  );




  (*  `!qs. FINITE qs ==> *)
  (*        (!aut a e a' e'. (!q. q ∈ qs ==> (a' q,e' q) ∈ (aut.trans q) ∧ a ⊆ a' q ∧ e' q ⊆ e) *)
  (*                    ∧ a ⊆ aut.alphabet *)
  (*         ==> (aut.alphabet ∩ BIGINTER {a' q | q ∈ qs },BIGUNION {e' q | q ∈ qs}) *)
  (*                     ∈ d_gen aut qs)` suffices_by *)
  (*      metis_tac[] *)
  (*  >> Induct_on `qs` >> rpt strip_tac >> fs[] *)
  (*    >- (fs[d_gen_def,d_conj_set_def] *)
  (*        >> metis_tac[FINITE_EMPTY,ITSET_def,IN_SING,EMPTY_SUBSET] *)
  (*       ) *)
  (*    >- (`(aut.alphabet ∩ BIGINTER {a' q | q ∈ qs}, *)
  (*          BIGUNION {e'' q | q ∈ qs}) ∈ d_gen aut qs` by metis_tac[] *)
  (*          >> PURE_ASM_REWRITE_TAC[d_gen_def,d_conj_set_def] *)
  (*          >> `{(q, aut.trans q) | q ∈ qs} DELETE (e, aut.trans e) = *)
  (*                        {(q,aut.trans q) | q ∈ qs}` *)
  (*                  by (fs[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac) *)
  (*          >> `FINITE {(q, aut.trans q) | q ∈ qs}` by metis_tac[IMAGE_FINITE,IMAGE_DEF] *)
  (*          >> imp_res_tac D_CONJ_SET_RECURSES *)
  (*          >> first_x_assum (qspec_then `(e, aut.trans e)` mp_tac) *)
  (*          >> rpt strip_tac *)
  (*          >> first_x_assum (qspec_then `{(aut.alphabet,{})}` mp_tac) *)
  (*          >> rpt strip_tac >> fs[] *)
  (*          >> rw[INSERT_LEMM] *)
  (*          >> `ITSET (d_conj o SND) ((e,aut.trans e) INSERT {(q,aut.trans q) | q ∈ qs}) *)
  (*                              {(aut.alphabet,∅)} = *)
  (*                  d_conj (aut.trans e) *)
  (*                         (ITSET (d_conj o SND) {(q, aut.trans q) | q ∈ qs} *)
  (*                                {(aut.alphabet,∅)})` *)
  (*                  by fs[] *)
  (*          >> `(e,aut.trans e) INSERT {(q,aut.trans q) | q ∈ qs} = *)
  (*                 {(q,aut.trans q) | (q = e) ∨ q ∈ qs}` by ( *)
  (*              simp[INSERT_DEF] >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac *)
  (*              >> metis_tac[] *)
  (*          ) *)
  (*          >> `(aut.alphabet ∩ BIGINTER {a' q | (q = e) ∨ q ∈ qs}, *)
  (*               BIGUNION {e'' q | (q = e) ∨ q ∈ qs}) ∈ *)
  (*                     d_conj (aut.trans e) *)
  (*                     (ITSET (d_conj ∘ SND) {(q,aut.trans q) | q ∈ qs} *)
  (*                            {(aut.alphabet,∅)})` suffices_by metis_tac[] *)
  (*          >> simp[d_conj_def] *)
  (*          >> qabbrev_tac `bigA = aut.alphabet ∩ BIGINTER {a' q | q ∈ qs}` *)
  (*          >> qabbrev_tac `bigE = BIGUNION {e'' q | q ∈ qs}` *)
  (*          >> qexists_tac `a' e` >> qexists_tac `bigA` *)
  (*          >> qexists_tac `e'' e` >> qexists_tac `bigE` *)
  (*          >> rpt strip_tac *)
  (*            >- (qunabbrev_tac `bigA` *)
  (*                >> `BIGINTER {a' q | (q = e) ∨ q ∈ qs} = a' e ∩ BIGINTER {a' q | q ∈ qs}` *)
  (*                  suffices_by metis_tac[INTER_ASSOC, INTER_COMM] *)
  (*                >> simp[SET_EQ_SUBSET,SUBSET_DEF,BIGINTER,INTER_DEF] >> rpt strip_tac *)
  (*                >> metis_tac[] *)
  (*               ) *)
  (*            >- (qunabbrev_tac `bigE` *)
  (*                >> simp[SET_EQ_SUBSET,SUBSET_DEF,BIGUNION,UNION_DEF] >> rpt strip_tac *)
  (*                >> metis_tac[] *)
  (*               ) *)
  (*            >- metis_tac[] *)
  (*            >- metis_tac[d_gen_def,d_conj_set_def] *)
  (*       ) *)
  (* ); *)

val D_GEN_A_E_LEMM3 = store_thm
  ("D_GEN_A_E_LEMM3",
   ``!qs a e aut q. FINITE qs ∧ (a,e) ∈ d_gen aut qs
  ==> (!q. q ∈ e ==> ?q' a' e'. q' ∈ qs ∧ (a',e') ∈ aut.trans q' ∧ q ∈ e' ∧ a ⊆ a')``,
  `!qs. FINITE qs ==> !a e q aut. q ∈ e ∧ (a,e) ∈ d_gen aut qs
   ==> ?q' a' e'. q' ∈ qs ∧ (a',e') ∈ aut.trans q' ∧ q ∈ e' ∧ a ⊆ a'`
  suffices_by metis_tac[]
  >> Induct_on `qs` >> rpt strip_tac >> fs[]
    >- fs[d_gen_def, d_conj_set_def,ITSET_THM]
    >- (POP_ASSUM mp_tac >> POP_ASSUM mp_tac
        >> PURE_ASM_REWRITE_TAC[d_gen_def,d_conj_set_def]
        >> rw[INSERT_LEMM]
        >> `{(q, aut.trans q) | q ∈ qs} DELETE (e, aut.trans e) = {(q,aut.trans q) | q ∈ qs}`
                   by (fs[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                       >> metis_tac[]
                      )
        >> `FINITE {(q,aut.trans q) | q ∈ qs}` by metis_tac[IMAGE_FINITE,IMAGE_DEF]
        >> imp_res_tac D_CONJ_SET_RECURSES
        >> first_x_assum (qspec_then `(e, aut.trans e)` mp_tac)
        >> rpt strip_tac
        >> first_x_assum (qspec_then `{(aut.alphabet,{})}` mp_tac)
        >> rpt strip_tac
        >> `ITSET (d_conj o SND) ((e,aut.trans e) INSERT {(q, aut.trans q) | q ∈ qs})
                                {(aut.alphabet,∅)} =
                   d_conj (aut.trans e)
                          (ITSET (d_conj o SND) {(q, aut.trans q) | q ∈ qs}
                                 {(aut.alphabet,∅)})` by fs[]
        >> `(a,e') ∈
               d_conj (aut.trans e)
               (ITSET (d_conj o SND) {(q, aut.trans q) | q ∈ qs} {(aut.alphabet,∅)})`
            by metis_tac[]
        >> POP_ASSUM mp_tac >> simp[d_conj_def]
        >> rpt strip_tac
        >> `q ∈ e1 \/ q ∈ e2` by metis_tac[IN_UNION]
           >- metis_tac[INTER_SUBSET]
           >- (`(a2,e2) ∈ d_gen aut qs` by metis_tac[d_gen_def,d_conj_set_def]
               >> `∃q' a' e'. q' ∈ qs ∧ (a',e') ∈ aut.trans q' ∧ q ∈ e' ∧ a2 ⊆ a'`
                  by metis_tac[]
               >> metis_tac[SUBSET_TRANS,INTER_SUBSET]
              )
       )
  );

val WAA2GBA_ISVALID = store_thm
  ("WAA2GBA_ISVALID",
   ``!aut. isVeryWeakAlterA aut
  ∧ isValidAlterA aut ∧ FINITE aut.states
  ==> isValidGBA (vwaa2gba aut)``,
   fs[vwaa2gba_def,isValidGBA_def,isValidAlterA_def] >> rpt strip_tac
     >- (fs[gba_trans_def, minimal_elements_def]
         >> `FINITE s` by metis_tac[IN_POW, PSUBSET_DEF, PSUBSET_FINITE]
         >> fs[IN_POW, SUBSET_DEF] >> rpt strip_tac
         >> `∃q' a' e'. q' ∈ s ∧ (a',e') ∈ aut.trans q' ∧ x ∈ e'`
             by metis_tac[D_GEN_A_E_LEMM3]
         >>  metis_tac[]
        )
     >- (fs[gba_trans_def, minimal_elements_def]
         >> `FINITE s` by metis_tac[IN_POW, PSUBSET_DEF, PSUBSET_FINITE]
         >> fs[IN_POW, SUBSET_DEF] >> rpt strip_tac
         >> Cases_on `s = {}`
            >- (`(a,d) = (aut.alphabet, {})` by (
              fs[d_gen_def, d_conj_set_def]
              >> fs[ITSET_THM, FINITE_EMPTY]
              )
              >> fs[])
            >- (imp_res_tac NONEMPTY_LEMM
               >> imp_res_tac D_GEN_A_E_LEMM
               >> `∃a' e'. (a',e') ∈ aut.trans e ∧ a ⊆ a' ∧ e' ⊆ d` by fs[]
               >> `∀x. x ∈ a' ⇒ x ∈ aut.alphabet` by metis_tac[IN_UNION,IN_SING]
               >> metis_tac[SUBSET_DEF]
               )
        )
     >- (fs[gba_accTrans_def] >> fs[])
     >- (fs[gba_accTrans_def] >> fs[])
  );

val vwaa2gba_gba_V_def = Define`
(vwaa2gba_gba_V waa_run v' 0 = waa_run.V 0)
∧ (vwaa2gba_gba_V waa_run v' (SUC i) = v' i (vwaa2gba_gba_V waa_run v' i))`;

val WAA_IN_GBA = store_thm
  ("GBA_IN_WAA",
   ``!aut. isVeryWeakAlterA aut ∧ FINITE aut.alphabet ∧ FINITE aut.states
     ∧ isValidAlterA aut
   ==> alterA_lang aut ⊆ GBA_lang (vwaa2gba aut)``,
   simp[SUBSET_DEF] >> rpt strip_tac
   >> fs[runForAA_def, alterA_lang_def, GBA_lang_def]
   >> `!i b. infBranchSuffOf run i b
         ==> ?b'. infBranchOf run b' /\ !j. (b j = b' (j+i))`
      by metis_tac[BRANCH_SUFF_LEMM]
   >> `∀b x. infBranchOf run b ∧ branchFixP b x ⇒ x ∉ aut.final`
      by metis_tac[BRANCH_ACC_LEMM]
   >> `word_range x ⊆ (vwaa2gba aut).alphabet` by (
       fs[vwaa2gba_def] >> metis_tac[SUBSET_DEF])
   >> `?r. isGBARunFor (vwaa2gba aut) r x` suffices_by metis_tac[]
   >> qabbrev_tac `min_dgen =
                 \qs. minimal_elements (d_gen aut qs)
                  (rrestrict (tr_less_general (all_acc_cond aut) qs)
                             (d_gen aut qs))`
  >> qabbrev_tac `less_gen = \qs. tr_less_general (all_acc_cond aut) qs`
  >> `?a_x. !i q. q ∈ run.V i ==>
             ((a_x i) q, run.E (i, q)) ∈ aut.trans q ∧ at x i ∈ (a_x i) q`
       by (
       fs[validAARunFor_def]
       >> `!i q. ?a. q ∈ run.V i ==> (a,run.E (i,q)) ∈ aut.trans q ∧ at x i ∈ a`
          by metis_tac[]
       >> `!i. ?f'. !q. q ∈ run.V i ==> (f' q, run.E (i, q)) ∈ aut.trans q ∧ at x i ∈ (f' q)`
          by metis_tac[SKOLEM_THM]
       >> metis_tac[SKOLEM_THM]
   )
   >> qabbrev_tac `e_old = (\i qs. BIGUNION {run.E (i,q) | q | q ∈ qs})`
   >> qabbrev_tac `a_old = (\i qs. aut.alphabet ∩ BIGINTER {a_x i q | q | q ∈ qs})`
   >> `?v' a'. !i qs. qs ⊆ run.V i ==>
         ((a' i) qs,(v' i) qs) ∈ min_dgen qs
         ∧ (((a' i) qs, (v' i) qs), a_old i qs, e_old i qs) ∈ less_gen qs`
        by (
           `!qs a e. (a,e) ∈ d_gen aut qs ∧ qs ⊆ aut.states ==>
                ∃a' e'. (a',e') ∈ min_dgen qs
                ∧ ((a',e'),a,e) ∈ less_gen qs`
             by metis_tac[D_GEN_HAS_MIN]
           >> `!i qs. ∃e_new a_new.
               (qs ⊆ run.V i) ==>
               (a_new,e_new) ∈ min_dgen qs
               ∧ ((a_new,e_new), a_old i qs, e_old i qs) ∈ less_gen qs`
                  by (
               fs[validAARunFor_def]
               >> rpt strip_tac >> rw[RIGHT_EXISTS_IMP_THM]
               >> `FINITE qs` by metis_tac[PSUBSET_DEF, PSUBSET_FINITE, SUBSET_TRANS]
               >> `(a_old i qs,e_old i qs) ∈ d_gen aut qs` by (
                   qunabbrev_tac `e_old` >> qunabbrev_tac `a_old` >> fs[]
                   >> HO_MATCH_MP_TAC D_GEN_A_E_LEMM2
                   >> rpt strip_tac >> fs[]
                   >> qexists_tac `aut.alphabet ∩ BIGINTER {a_x i q | q | q ∈ qs}`
                   >> qexists_tac `BIGUNION {run.E (i,q) | q | q ∈ qs}`
                   >> rpt strip_tac
                         >- metis_tac[SUBSET_DEF]
                         >- (simp[SUBSET_DEF, BIGINTER, INTER_DEF] >> rpt strip_tac
                                 >> metis_tac[])
                         >- (simp[BIGUNION,SUBSET_DEF] >> rpt strip_tac >> metis_tac[])
                         >- (simp[BIGINTER,SUBSET_DEF,INTER_DEF] >> rpt strip_tac)
               )
           >> metis_tac[SUBSET_TRANS]
           )
           >> metis_tac[SKOLEM_THM]
   )
   >> `?r. isValidGBARunFor (vwaa2gba aut) r x
         ∧ (isValidGBARunFor (vwaa2gba aut) r x ==> isAcceptingGBARunFor (vwaa2gba aut) r x)`
       suffices_by metis_tac[isGBARunFor_def]
   >> qexists_tac `GBA_RUN (vwaa2gba_gba_V run v')` >> rpt strip_tac
   >> `!n. v' n (vwaa2gba_gba_V run v' n) ⊆ run.V (n+1)` by (
       fs[validAARunFor_def]
       >> Induct_on `n`
        >- (fs[vwaa2gba_gba_V_def]
            >> `∃a_new.
                (run.V 0) ⊆ run.V 0 ⇒
                (a_new,v' 0 (run.V 0)) ∈ min_dgen (run.V 0)
                ∧ ((a_new,v' 0 (run.V 0)),a_old 0 (run.V 0),e_old 0 (run.V 0))
                           ∈ less_gen (run.V 0)`
               by metis_tac[]
            >> fs[tr_less_general_def] >> qunabbrev_tac `less_gen`
            >> qunabbrev_tac `a_old` >> qunabbrev_tac `e_old` >> fs[]
            >> simp[SUBSET_DEF] >> rpt strip_tac >> fs[BIGUNION,SUBSET_DEF]
            >> `?q. x' ∈ run.E(0,q)` by metis_tac[]
            >> metis_tac[DECIDE ``0 + 1 = 1``]
           )
        >- (fs[vwaa2gba_gba_V_def]
            >> qabbrev_tac `e = (vwaa2gba_gba_V run v' n)`
            >> `∃a_new.
              (a_new,v' (n + 1) (v' n e)) ∈ min_dgen (v' n e)
              ∧ ((a_new,v' (n + 1) (v' n e)),a_old (n + 1) (v' n e),e_old (n+1) (v' n e)) ∈
                      less_gen (v' n e)` by metis_tac[]
            >> fs[tr_less_general_def] >> qunabbrev_tac `less_gen` >> fs[]
            >> qunabbrev_tac `e_old` >> fs[]
            >> fs[BIGUNION,SUBSET_DEF] >> rpt strip_tac
            >> `?q. x' ∈ run.E (n+1,q)` by metis_tac[SUC_ONE_ADD,ADD_COMM]
            >> metis_tac[SUBSET_TRANS,ADD_SUC,ADD_COMM,SUC_ONE_ADD]
           )
   )
   >> `!n. vwaa2gba_gba_V run v' n ⊆ run.V n` by (
       Cases_on `n` >> fs[vwaa2gba_gba_V_def]
       >> metis_tac[DECIDE ``n' + 1 = SUC n'``]
   )
    >- (fs[isValidGBARunFor_def, vwaa2gba_gba_V_def, vwaa2gba_def,validAARunFor_def]
        >> rpt strip_tac
        >> rw[DECIDE ``i + 1 = SUC i``] >> fs[vwaa2gba_gba_V_def]
        >> simp[gba_trans_def]
        >> qabbrev_tac `e = vwaa2gba_gba_V run v' i`
        >> qexists_tac `a' i e` >> fs[]
        >> qunabbrev_tac `less_gen` >> fs[tr_less_general_def]
        >> `at x i ∈ a_old i e` by (
             qunabbrev_tac `a_old` >> fs[] >> rpt strip_tac
              >- metis_tac[AT_WORD_RANGE, SUBSET_DEF]
              >- (qunabbrev_tac `e` >> `q ∈ run.V i` by fs[SUBSET_DEF]
                  >> metis_tac[])
         )
        >> metis_tac[SUBSET_DEF]
       )
    >- (rw[GBA_ACC_LEMM]
        >> `isValidGBA (vwaa2gba aut)` by metis_tac[WAA2GBA_ISVALID]
        >> qabbrev_tac `a'_i = \i. a' i (vwaa2gba_gba_V run v' i)`
        >> `!j. (a'_i j,vwaa2gba_gba_V run v' (j + 1)) ∈
                       (vwaa2gba aut).trans (vwaa2gba_gba_V run v' j)
                       ∧ at x j ∈ a'_i j` by (
            rpt strip_tac
             >- (simp[vwaa2gba_def, gba_trans_def, vwaa2gba_gba_V_def, DECIDE ``j+1=SUC j``]
                 >> metis_tac[])
             >- (qabbrev_tac `e = vwaa2gba_gba_V run v' j`
                 >> qunabbrev_tac `less_gen` >> fs[tr_less_general_def]
                 >> `at x j ∈ a_old j e` by (
                      qunabbrev_tac `a_old` >> fs[] >> rpt strip_tac
                       >- metis_tac[AT_WORD_RANGE, SUBSET_DEF]
                       >- (qunabbrev_tac `e` >> `q ∈ run.V j` by fs[SUBSET_DEF]
                           >> metis_tac[])
                  )
                 >> qunabbrev_tac `a'_i` >> fs[]
                 >> metis_tac[SUBSET_DEF])
         )
        >> `T' ∈ (gba_accTrans aut)` by (
             fs[vwaa2gba_def]
             >> `T' ∈ (GBA (POW aut.states) aut.initial (gba_trans aut)
                        (gba_accTrans aut) aut.alphabet).accTrans` by metis_tac[]
             >> fs[]
         )
        >> fs[gba_accTrans_def] >> rw[] >> qabbrev_tac `T' = acc_cond aut f`
        >> fs[acc_cond_def]
        >> `!j. ~((vwaa2gba_gba_V run v' j,a'_i j,vwaa2gba_gba_V run v' (j + 1)) ∈ T')
               ∧ (f ∈ vwaa2gba_gba_V run v' j)
                ==> f ∈ run.E (j, f)` by (
             rpt strip_tac >> `f ∈ run.V j` by metis_tac[SUBSET_DEF]
             >> qabbrev_tac `e = vwaa2gba_gba_V run v' j`
             >> qabbrev_tac `e' = vwaa2gba_gba_V run v' (j + 1)`
             >> `~((e,a_old j e, e_old j e) ∈ T')` by (
                 `((a' j e, e'), a_old j e, e_old j e) ∈ less_gen e` by (
                     qunabbrev_tac `e` >> qunabbrev_tac `a'_i`
                     >> qunabbrev_tac `e'` >> fs[]
                     >> simp[vwaa2gba_gba_V_def, DECIDE ``j+1=SUC j``]
                 )
                 >> qunabbrev_tac `less_gen` >> fs[tr_less_general_def]
                 >> qunabbrev_tac `a'_i` >> fs[]
                 >> `T' ∈ all_acc_cond aut` suffices_by metis_tac[]
                 >> qunabbrev_tac `T'` >> simp[all_acc_cond_def]
                 >> qexists_tac `f` >> simp[acc_cond_def]
             )
             >> `~(f ∉ (e_old j e) ∨
                    ∃b e''.
                    (b,e'') ∈ aut.trans f ∧ (a_old j e) ⊆ b ∧ f ∉ e''
                    ∧ e'' ⊆ (e_old j e))`
                 by (
                 qunabbrev_tac `T'` >> fs[]
                  >- metis_tac[IN_POW,SUBSET_TRANS,validAARunFor_def]
                  >- metis_tac[IN_POW,SUBSET_TRANS,validAARunFor_def]
                  >- metis_tac[IN_POW,SUBSET_TRANS,validAARunFor_def]
                  >- metis_tac[IN_POW,SUBSET_TRANS,validAARunFor_def]
                  >- metis_tac[IN_POW,SUBSET_TRANS,validAARunFor_def]
                  >- metis_tac[IN_POW,SUBSET_TRANS,validAARunFor_def]
                  >- metis_tac[IN_POW,SUBSET_TRANS,validAARunFor_def]
                  >- (`e_old j e ∈ POW aut.states` suffices_by fs[]
                      >> qunabbrev_tac `e_old` >> fs[IN_POW,BIGUNION,validAARunFor_def]
                      >> fs[SUBSET_DEF] >> metis_tac[SUBSET_DEF])
                  >- (`a_old j e ∈ POW aut.alphabet` suffices_by fs[]
                      >> qunabbrev_tac `a_old` >> fs[IN_POW,BIGUNION, validAARunFor_def]
                     )
                  >- metis_tac[IN_POW,SUBSET_TRANS,validAARunFor_def]
                  >- (`e_old j e ∈ POW aut.states` suffices_by fs[]
                      >> qunabbrev_tac `e_old` >> fs[IN_POW,BIGUNION,validAARunFor_def]
                      >> fs[SUBSET_DEF] >> metis_tac[SUBSET_DEF])
                  >- (`a_old j e ∈ POW aut.alphabet` suffices_by fs[]
                      >> qunabbrev_tac `a_old` >> fs[IN_POW,BIGUNION, validAARunFor_def]
                     )
             )
             >> fs[]
             >> first_x_assum (qspec_then `a_x j f` mp_tac) >> rpt strip_tac
             >> first_x_assum (qspec_then `run.E(j,f)` mp_tac) >> rpt strip_tac
               >- metis_tac[]
               >- (qunabbrev_tac `a_old` >> fs[]
                   >> `aut.alphabet ∩ BIGINTER {a_x j q | q ∈ e} ⊆ a_x j f` suffices_by fs[]
                   >> fs[SUBSET_DEF,BIGINTER,INTER_DEF] >> rpt strip_tac >> metis_tac[]
                  )
               >- (`run.E (j,f) ⊆ e_old j e` suffices_by fs[]
                   >> qunabbrev_tac `e_old` >> fs[SUBSET_DEF,BIGUNION] >> rpt strip_tac
                   >> metis_tac[]
                  )
         )
        >> Cases_on `f ∈ vwaa2gba_gba_V run v' (i + 1)`
          >- (`(!j. i <= j ==>
                ~((vwaa2gba_gba_V run v' j, a'_i j, vwaa2gba_gba_V run v' (j+1)) ∈ T'))
          ==> !j. i <= j ==> f ∈ vwaa2gba_gba_V run v' (j+1)` by (
          rpt strip_tac >> qunabbrev_tac `T'` >> first_x_assum (qspec_then `j` mp_tac)
          >> rpt strip_tac >> fs[] >> POP_ASSUM mp_tac >> simp[] >> rpt strip_tac
            >- metis_tac[validAARunFor_def, IN_POW, SUBSET_TRANS]
            >- metis_tac[validAARunFor_def, IN_POW, SUBSET_TRANS]
            >- (qabbrev_tac `e = vwaa2gba_gba_V run v' j`
                >> qabbrev_tac `e' = vwaa2gba_gba_V run v' (j + 1)`
                >> `(a'_i j, e') ∈ (vwaa2gba aut).trans e` by metis_tac[]
                >> `a'_i j ⊆ aut.alphabet` suffices_by metis_tac[IN_POW]
                >> `a'_i j ⊆ (vwaa2gba aut).alphabet` suffices_by simp[vwaa2gba_def]
                >> `e ∈ (vwaa2gba aut).states` suffices_by metis_tac[isValidGBA_def]
                >> qunabbrev_tac `e` >> fs[]
                >> `vwaa2gba_gba_V run v' j ⊆ aut.states` suffices_by (
                     simp[vwaa2gba_def] >> metis_tac[IN_POW]
                 )
                >> metis_tac[validAARunFor_def,SUBSET_TRANS]
               )
           )
          >> CCONTR_TAC >> fs[]
          >> `!j. ¬(i ≤ j) ∨
                 (vwaa2gba_gba_V run v' j,a'_i j,vwaa2gba_gba_V run v' (j + 1)) ∉ T'`
             by (rpt strip_tac
               >> first_x_assum (qspec_then `a'_i j` mp_tac) >> simp[vwaa2gba_def]
               >> `(a'_i j,vwaa2gba_gba_V run v' (j + 1)) ∈
                   (vwaa2gba aut).trans (vwaa2gba_gba_V run v' j) ∧ at x j ∈ a'_i j`
                   by fs[] >> fs[vwaa2gba_def]
               >> `(a'_i j,vwaa2gba_gba_V run v' (j + 1)) ∈
                   (GBA (POW aut.states) aut.initial (gba_trans aut)
                        (gba_accTrans aut) aut.alphabet).trans
                   (vwaa2gba_gba_V run v' j)` by metis_tac[] >> fs[]
               >> rpt strip_tac
               >> `vwaa2gba_gba_V run v' j ∈ POW aut.states` by (
                      `vwaa2gba_gba_V run v' j ⊆ run.V j` by fs[]
                      >> fs[validAARunFor_def]
                      >> metis_tac[IN_POW,SUBSET_TRANS]
                  )
               >> metis_tac[]
                )
          >> `∀j. i ≤ j ⇒ f ∈ vwaa2gba_gba_V run v' (j + 1)` by metis_tac[]
          >> `!j. i <= j ==> f ∈ run.E (j+1, f)`
             by metis_tac[DECIDE ``i <= j ==> i <= j + 1``]
          >> `infBranchSuffOf run (i+1) (\n. f)` by (
                simp[infBranchSuffOf_def] >> rpt strip_tac
                    >- metis_tac[DECIDE ``i <= i``,SUBSET_DEF]
                    >- metis_tac[DECIDE ``i <= i + n``, ADD_ASSOC]
          )
          >> imp_res_tac BRANCH_SUFF_LEMM
          >> fs[] >> imp_res_tac BRANCH_ACC_LEMM
          >> `branchFixP b' f` by (
               simp[branchFixP_def] >> qexists_tac `i + 1`
               >> fs[] >> rpt strip_tac
                 >- metis_tac[DECIDE ``i + (0 + 1) = i + 1``]
                 >- (`i + 1 <= m` by simp[]
                     >> `?k. k + (i + 1) = m`
                       by metis_tac[LESS_EQ_ADD_EXISTS]
                     >> metis_tac[ADD_ASSOC,ADD_COMM]
                    )
          )
          >> metis_tac[]
             )
          >- (`?j a. i <= j
              ∧ (vwaa2gba_gba_V run v' j, a, vwaa2gba_gba_V run v' (j + 1)) ∈ T'
          ∧ (a, vwaa2gba_gba_V run v' (j + 1)) ∈
                     (vwaa2gba aut).trans (vwaa2gba_gba_V run v' j)
          ∧ (vwaa2gba_gba_V run v' j ∈ POW aut.states)
          ∧ at x j ∈ a`
               suffices_by (simp[vwaa2gba_def] >> metis_tac[])
               >> qexists_tac `i`
               >> qexists_tac `a'_i i` >> fs[]
               >> qunabbrev_tac `T'` >> fs[] >> rpt strip_tac
                 >- metis_tac[validAARunFor_def, IN_POW, SUBSET_TRANS]
                 >- metis_tac[validAARunFor_def, IN_POW, SUBSET_TRANS]
                 >- (qabbrev_tac `e = vwaa2gba_gba_V run v' i`
                     >> qabbrev_tac `e' = vwaa2gba_gba_V run v' (i + 1)`
                     >> `(a'_i i, e') ∈ (vwaa2gba aut).trans e` by metis_tac[]
                     >> `e ∈ (vwaa2gba aut).states` suffices_by (
                          fs[isValidGBA_def] >> strip_tac
                          >> `a'_i i ⊆ aut.alphabet` suffices_by metis_tac[IN_POW]
                          >> `a'_i i ⊆ (vwaa2gba aut).alphabet` suffices_by fs[vwaa2gba_def]
                          >> metis_tac[]
                      )
                     >> simp[vwaa2gba_def] >> qunabbrev_tac `e`
                     >> metis_tac[SUBSET_TRANS,IN_POW,validAARunFor_def]
                    )
                 >- (`vwaa2gba_gba_V run v' j ⊆ run.V j` by fs[]
                     >> fs[validAARunFor_def]
                     >> metis_tac[IN_POW,SUBSET_TRANS])
             )
       )
  );

val waa_run_branch_cond_def = Define`
  waa_run_branch_cond f aut q i x a =
          (f i, a, f (i+1)) ∈ acc_cond aut q
           ∧ q ∈ aut.final
           ∧ (a, f (i + 1)) ∈ (vwaa2gba aut).trans (f i)
           ∧ at x i ∈ a`;

val waa_run_E_def = Define`
  waa_run_E x waa f e_x e_x' (i,q) =
          if (?a. waa_run_branch_cond f waa q i x a)
          then e_x' i ($@ (waa_run_branch_cond f waa q i x)) q
          else e_x i q`;

val GBA_IN_WAA = store_thm
  ("GBA_IN_WAA",
  ``!aut. isVeryWeakAlterA aut ∧ FINITE aut.alphabet ∧ FINITE aut.states
  ∧ isValidAlterA aut ==> GBA_lang (vwaa2gba aut) ⊆ alterA_lang aut``,
  simp[SUBSET_DEF] >> rpt strip_tac >> fs[alterA_lang_def, GBA_lang_def,isGBARunFor_def]
  >> Cases_on `r`
  >> fs[isValidGBARunFor_def]
  >> qabbrev_tac `fullAuto =  GBA (POW aut.states) aut.initial (gba_trans aut)
                                  (gba_accTrans aut) aut.alphabet`
  >> qabbrev_tac `min_dgen =
        \qs. minimal_elements (d_gen aut qs)
         (rrestrict (tr_less_general (gba_accTrans aut) qs) (d_gen aut qs))`
  >> `!i. ∃a. (a,f (SUC i)) ∈ d_gen aut (f i) ∧ at x i ∈ a` by (
        strip_tac >> fs[vwaa2gba_def]
        >> `!i'. ?a. (a, f (i' + 1)) ∈ fullAuto.trans (f i') ∧ at x i' ∈ a` by metis_tac[]
        >> qunabbrev_tac `min_dgen` >> qunabbrev_tac `fullAuto`
        >> fs[gba_trans_def,minimal_elements_def]
        >> metis_tac[SUC_ONE_ADD,ADD_COMM]
  )
  >> `!i. f i ∈ (POW aut.states)` by (
      Induct_on `i`
       >- (fs[vwaa2gba_def,isValidAlterA_def]
           >> `f 0 ∈ fullAuto.initial` by metis_tac[] >> qunabbrev_tac `fullAuto`
           >> fs[] >> metis_tac[IN_POW,SUBSET_DEF]
          )
       >- (`FINITE (f i)` by metis_tac[IN_POW,PSUBSET_DEF,PSUBSET_FINITE]
           >> first_x_assum (qspec_then `i` mp_tac) >> rpt strip_tac
           >> imp_res_tac D_GEN_A_E_LEMM3
           >> rw[IN_POW] >> fs[SUBSET_DEF] >> rpt strip_tac
           >> first_x_assum (qspec_then `x'` mp_tac) >> rpt strip_tac
           >> `∃q' a' e'.
               q' ∈ f i ∧ (a',e') ∈ aut.trans q' ∧ x' ∈ e' ∧
               ∀x. x ∈ a ⇒ x ∈ a'` by fs[]
           >> metis_tac[isValidAlterA_def,IN_POW,SUBSET_DEF]
          )
  )
  >> `!i. FINITE (f i)` by metis_tac[IN_POW,PSUBSET_DEF,PSUBSET_FINITE]
  >> `!i. ?a. (!q. q ∈ (f i)
         ==> ?a' e'. (a',e') ∈ aut.trans q ∧ (a ⊆ a') ∧ e' ⊆ f (i + 1))
         ∧ at x i ∈ a`
     by metis_tac[D_GEN_A_E_LEMM,SUC_ONE_ADD,ADD_COMM]
  >> `?e_x. !i. ?a. (!q. q ∈ f i ==>
         ?a'. (a',(e_x i) q) ∈ aut.trans q ∧ a ⊆ a' ∧ (e_x i) q ⊆ f (i + 1))
         ∧ at x i ∈ a`
       by metis_tac[SKOLEM_THM]
  >> `?e_x'. !i a q. q ∈ f i ∧ (f i, a, f (i+1)) ∈ acc_cond aut q
         ∧ q ∈ aut.final
         ∧ (a, f (i + 1)) ∈ (vwaa2gba aut).trans (f i)
         ∧ at x i ∈ a
         ==> ?a'. (a', ((e_x' i) a) q) ∈ aut.trans q
              ∧ ~(q ∈ e_x' i a q) ∧ e_x' i a q ⊆ f (i + 1) ∧ a ⊆ a'` by (
       `∀i a q. q ∈ f i ∧
         (f i,a,f (i + 1)) ∈ acc_cond aut q ∧ q ∈ aut.final
         ∧ (a, f (i+1)) ∈ (vwaa2gba aut).trans (f i)
         ⇒ ∃a' e'.
         (a',e') ∈ aut.trans q ∧ ~(q ∈ e') ∧ e' ⊆ f (i + 1) ∧ a ⊆ a'` by (
            rpt strip_tac >> fs[acc_cond_def,vwaa2gba_def] >> fs[]
            >> `(a, f (i+1)) ∈ fullAuto.trans (f i)` by metis_tac[]
            >> qunabbrev_tac `fullAuto` >> fs[gba_trans_def]
            >> `(a, f (i + 1)) ∈ d_gen aut (f i)` by fs[minimal_elements_def, gba_trans_def]
            >> `∃a' e'. (a',e') ∈ aut.trans q ∧ a ⊆ a' ∧ e' ⊆ f (i + 1)`
                    by metis_tac[D_GEN_A_E_LEMM]
            >> metis_tac[SUBSET_DEF]
       )
       >> metis_tac[SKOLEM_THM]
  )
  >> qabbrev_tac
     `r = run_restr (f 0)
            (ALTERA_RUN f (λ(i,q). if q ∈ f i
                            then waa_run_E x aut f e_x e_x' (i,q) else {}))`
  >> qexists_tac `r`
  >> `!i. r.V i ⊆ f i` by (
      Induct_on `i`
        >- (qunabbrev_tac `r` >> fs[run_restr_def, run_restr_V_def])
        >- (qunabbrev_tac `r` >> fs[SUBSET_DEF] >> rpt strip_tac
            >> fs[run_restr_def, run_restr_V_def]
            >> `q ∈ f i ∧ (s = waa_run_E x aut f e_x e_x' (i,q))`
                by metis_tac[MEMBER_NOT_EMPTY]
            >> fs[waa_run_E_def]
            >> Cases_on `?a. waa_run_branch_cond f aut q i x a`
              >- (fs[] >> first_x_assum (qspec_then `i` mp_tac) >> rpt strip_tac
                  >> qabbrev_tac `a' = $@ (waa_run_branch_cond f aut q i x)`
                  >> first_x_assum (qspec_then `a'` mp_tac) >> rpt strip_tac
                  >> first_x_assum (qspec_then `q` mp_tac) >> rpt strip_tac
                  >> `waa_run_branch_cond f aut q i x a'` by (
                       qunabbrev_tac `a'` >> metis_tac[SELECT_THM]
                   )
                  >> fs[waa_run_branch_cond_def]
                  >> metis_tac[SUC_ONE_ADD,ADD_COMM]
                 )
              >- metis_tac[SUC_ONE_ADD,ADD_COMM]
           )
  )
  >> simp[runForAA_def]
  >> `(validAARunFor aut r x ∧ (validAARunFor aut r x ==> acceptingAARun aut r))
                                ∧ word_range x ⊆ aut.alphabet`
      suffices_by metis_tac[]
  >> simp[runForAA_def, run_restr_def, run_restr_V_def, run_restr_E_def] >> rpt strip_tac
   >- (simp[validAARunFor_def] >> rpt strip_tac
      >- (fs[vwaa2gba_def, run_restr_V_def]
          >> `f 0 ∈ fullAuto.initial` by metis_tac[] >> qunabbrev_tac `fullAuto`
          >> fs[] >> qunabbrev_tac `r` >> fs[run_restr_def, run_restr_V_def])
      >- metis_tac[IN_POW,SUBSET_TRANS]
      >- (Cases_on `?a. waa_run_branch_cond f aut q i x a`
           >- (fs[] >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
               >> first_x_assum (qspec_then `i` mp_tac) >> rpt strip_tac
               >> qabbrev_tac `a' = $@ (waa_run_branch_cond f aut q i x)`
               >> first_x_assum (qspec_then `a'` mp_tac) >> rpt strip_tac
               >> first_x_assum (qspec_then `q` mp_tac) >> rpt strip_tac
               >> `waa_run_branch_cond f aut q i x a'` by (
                    qunabbrev_tac `a'` >> metis_tac[SELECT_THM]
                )
               >> `q ∈ f i` by metis_tac[SUBSET_DEF]
               >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac >> simp[waa_run_branch_cond_def]
               >> rpt strip_tac >> fs[]
               >> qexists_tac `a''` >> fs[]
               >> qunabbrev_tac `r` >> fs[]
               >> fs[run_restr_def, run_restr_E_def, waa_run_E_def]
               >> metis_tac[SUBSET_DEF])
           >- (`∃a a'. (a',e_x i q) ∈ aut.trans q ∧ a ⊆ a' ∧ e_x i q ⊆ f (i + 1)
                  ∧ at x i ∈ a` by metis_tac[SUBSET_DEF]
               >> qexists_tac `a'` >> fs[] >> `q ∈ f i` by metis_tac[SUBSET_DEF]
               >> qunabbrev_tac `r` >> fs[]
               >> fs[run_restr_def, run_restr_E_def, waa_run_E_def]
               >> metis_tac[SUBSET_DEF]
              )
         )
      >- (Cases_on `q ∈ r.V i`
           >- (`q ∈ f i` by metis_tac[SUBSET_DEF]
               >> fs[SUBSET_DEF] >> rpt strip_tac
               >> qunabbrev_tac `r` >> fs[run_restr_def, run_restr_E_def]
               >> `x' ∈ waa_run_E x aut f e_x e_x' (i,q)` by metis_tac[MEMBER_NOT_EMPTY]
               >> fs[waa_run_E_def]
               >> simp[DECIDE ``i + 1 = SUC i``, run_restr_V_def]
               >> Cases_on `?a. waa_run_branch_cond f aut q i x a`
                 >- (fs[]
                     >> qabbrev_tac `a' = $@ (waa_run_branch_cond f aut q i x)`
                     >> qexists_tac `e_x' i a' q` >> strip_tac >> fs[]
                     >> qexists_tac `q` >> metis_tac[]
                    )
                 >- metis_tac[]
              )
           >- (qunabbrev_tac `r` >> fs[run_restr_def,run_restr_E_def])
         )
      >- (Cases_on `i = 0` >> fs[] >> `q ∈ f i` by metis_tac[SUBSET_DEF]
          >> `?j. i = SUC j` by (Cases_on `i` >> fs[])
          >> rw[] >> qunabbrev_tac `r`
          >> fs[run_restr_def, run_restr_E_def, run_restr_V_def, waa_run_E_def]
          >> qexists_tac `q'` >> metis_tac[]
         )
      )
   >- (`∀b x. infBranchOf r b ∧ branchFixP b x ⇒ x ∉ aut.final`
         suffices_by metis_tac[BRANCH_ACC_LEMM]
       >> rpt strip_tac
       >> `∀T. T ∈ (vwaa2gba aut).accTrans
          ⇒ ∀i. ∃a j. i ≤ j ∧ (f j,a,f (j + 1)) ∈ T
          ∧ (a, f (j+1)) ∈ (vwaa2gba aut).trans (f j)
          ∧ at x j ∈ a`
          by metis_tac[GBA_ACC_LEMM]
       >> fs[branchFixP_def]
       >> `?j. j >= i ∧ ~(b j = x')` suffices_by metis_tac[]
       >> qabbrev_tac
           `realTrans = {(e',a,e) | (a,e) ∈ gba_trans aut e'
                                          ∧ e' ∈ POW aut.states}`
       >> `!T. T ∈ {acc_cond aut f ∩ realTrans |
                    f | f ∈ aut.final } ==>
                      !i. ?a j. i <= j ∧ (f j, a, f (j +1)) ∈ T
                       ∧ (a, f (j+1)) ∈ (vwaa2gba aut).trans (f j)
                       ∧ at x j ∈ a` by(
             rpt strip_tac
             >> first_x_assum (qspec_then `T'` mp_tac) >> rpt strip_tac
             >> `T' ∈ (vwaa2gba aut).accTrans` by (
                 simp[vwaa2gba_def] >> qunabbrev_tac `fullAuto`
                 >> fs[] >> simp[gba_accTrans_def] >> metis_tac[]
             )
             >> fs[]
       )
       >> first_x_assum (qspec_then `acc_cond aut x' ∩ realTrans` mp_tac)
       >> rpt strip_tac
       >> fs[]
       >> `∀i. ∃a j. i ≤ j ∧ (f j,a,f (j + 1)) ∈ acc_cond aut x'
                       ∧ (f j,a,f (j+1)) ∈ realTrans
                       ∧ (a,f (j + 1)) ∈ (vwaa2gba aut).trans (f j)
                       ∧ at x j ∈ a`
                   by metis_tac[]
       >> first_x_assum (qspec_then `i` mp_tac) >> rpt strip_tac
       >> `j >= i` by simp[]
       >> `x' ∈ r.V j` by metis_tac[BRANCH_V_LEMM]
       >> `~(x' ∈ r.E(j,x'))` by (
           `x' ∈ f j` by metis_tac[SUBSET_DEF]
           >> `waa_run_branch_cond f aut x' j x a` by metis_tac[waa_run_branch_cond_def]
           >> qabbrev_tac `a' = $@ (waa_run_branch_cond f aut x' j x)`
           >> `waa_run_branch_cond f aut x' j x a'` by (
               qunabbrev_tac `a'` >> metis_tac[SELECT_THM]
           )
           >> `~(x' ∈ e_x' j a' x')` suffices_by (
               qunabbrev_tac `r` >> fs[] >> rpt strip_tac
               >> fs[run_restr_def, run_restr_E_def, run_restr_V_def, waa_run_E_def]
               >> metis_tac[MEMBER_NOT_EMPTY]
           )
           >> POP_ASSUM mp_tac >> simp[waa_run_branch_cond_def] >> metis_tac[]
       )
       >> `(b j = x') ∧ (b (j + 1) = x')` by simp[]
       >> metis_tac[infBranchOf_def]
      )
   >- (`(vwaa2gba aut).alphabet = aut.alphabet`
           by (simp[vwaa2gba_def] >> qunabbrev_tac `fullAuto` >> fs[])
       >> metis_tac[SUBSET_TRANS]
      )
  );

val GBA_CORRECT = store_thm
  ("GBA_CORRECT",
   ``!aut. isVeryWeakAlterA aut ∧ FINITE aut.alphabet ∧ FINITE aut.states
     ∧ isValidAlterA aut ==> (GBA_lang (vwaa2gba aut) = alterA_lang aut)``,
   metis_tac[WAA_IN_GBA, GBA_IN_WAA,SET_EQ_SUBSET]
  );

val _ = export_theory()
