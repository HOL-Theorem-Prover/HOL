open HolKernel Parse boolLib bossLib;

open arithmeticTheory whileTheory logrootTheory pred_setTheory listTheory
open reductionEval;
open churchoptionTheory churchlistTheory recfunsTheory
     kolmogorov_complexityTheory invarianceResultsTheory boolListsTheory
open churchDBTheory
open recursivefnsTheory primrecfnsTheory prtermTheory
open unary_recfnsTheory

val _ = new_theory "pfreefns";

val _ = intLib.deprecate_int()

Theorem bnf_of_SOME_lameq:
  bnf_of M = SOME N ⇔ M == N ∧ bnf N
Proof
  eq_tac
  >- (strip_tac >> drule normal_orderTheory.bnf_of_SOME >>
      simp_tac (bsrw_ss())[]) >>
  ACCEPT_TAC normal_orderTheory.lameq_bnf_of_SOME_I
QED

Definition calc_fn_alist_def :
  calc_fn_alist =
  LAM "M" (
    LAM "s" (
      LAM "l" (
        cmap @@ (
          LAM "it" (cpair @@ (cfst @@ VAR "it")
                          @@ (cforce_num @@ (csnd @@ VAR "it")))
        ) @@ (
          cfilter @@ (LAM "it" (cbnf @@ (csnd @@ VAR "it"))) @@ VAR "l"
        )
      ) @@ ( (* generate list of all step-results *)
        ctabulate @@
          VAR "s" @@
          LAM "i" (
            cpair @@ VAR "i" @@ (
              csteps @@ VAR "s" @@ (
                cdAPP @@ (cnumdB @@ VAR "M")
                      @@ (cchurch @@ VAR "i")
              )
            )
          )
      )
    )
  )
End

Theorem FV_calc_fn_alist[simp]:
  FV calc_fn_alist = ∅
Proof
  simp[EXTENSION, calc_fn_alist_def]
QED

Theorem calc_fn_alist_eqn = brackabs.brackabs_equiv [] calc_fn_alist_def;

Theorem bnf_of_cnil[simp]:
  bnf_of cnil = SOME cnil
Proof
  simp[normal_orderTheory.bnf_bnf_of, cnil_def]
QED

Theorem steps_LAM[simp]:
  ∀n M. steps n (LAM v M) = LAM v (steps n M)
Proof
  Induct >> simp[normal_orderTheory.noreduct_thm] >> rw[] >>
  Cases_on ‘noreduct M’ >>
  fs[normal_orderTheory.noreduct_bnf]
QED

Theorem steps_VARAPP[simp]:
  ∀n M s. steps n (VAR s @@ M) = VAR s @@ steps n M
Proof
  Induct >> simp[normal_orderTheory.noreduct_thm] >> rw[] >>
  Cases_on ‘noreduct M’ >> fs[normal_orderTheory.noreduct_bnf]
QED

Theorem bnf_of_LAM:
  bnf_of (LAM v M0) = do M <- bnf_of M0 ; SOME (LAM v M) od
Proof
  Cases_on ‘bnf_of M0’ >> simp[]
  >- fs[numsAsCompStatesTheory.bnf_of_EQ_NONE_steps] >>
  fs[stepsTheory.bnf_steps] >> metis_tac[]
QED

Theorem bnf_of_VAR[simp]:
  bnf_of (VAR s) = SOME (VAR s)
Proof
  simp[normal_orderTheory.bnf_bnf_of]
QED

Theorem bnf_of_VARAPP:
  bnf_of (VAR s @@ M0) = do M <- bnf_of M0 ; SOME (VAR s @@ M) od
Proof
  Cases_on ‘bnf_of M0’ >> simp[]
  >- fs[numsAsCompStatesTheory.bnf_of_EQ_NONE_steps] >>
  fs[stepsTheory.bnf_steps] >> metis_tac[]
QED

Theorem steps_VARAPP2a:
  ∀m n M0.
     bnf (steps n M0) ∧ m ≤ n ∧ (∀i. i < n ⇒ ¬bnf (steps i M0)) ⇒
     steps m (VAR s @@ M0 @@ N0) = VAR s @@ steps m M0 @@ N0
Proof
  Induct >> rw[] >> fs[]
  >- (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[]) >>
  simp[normal_orderTheory.noreduct_thm] >> Cases_on ‘noreduct M0’ >> simp[]
  >- fs[normal_orderTheory.noreduct_bnf] >>
  first_x_assum irule >> qexists_tac ‘n - 1’ >> simp[] >>
  Cases_on ‘n’ >> fs[] >> rfs[] >> qx_gen_tac ‘i’ >>
  first_x_assum (qspec_then ‘SUC i’ mp_tac) >> simp[]
QED

Theorem steps_VARAPP2b:
  ∀m n M0 N0.
    bnf (steps n M0) ∧ n < m ∧ (∀i. i < n ⇒ ¬bnf (steps i M0)) ⇒
    steps m (VAR s @@ M0 @@ N0) = VAR s @@ steps n M0 @@ steps (m - n) N0
Proof
  Induct >> rw[] >> fs[]
  >- (Cases_on ‘n’ >> simp[])
  >- (Cases_on ‘SUC m - n’ >> simp[])
  >- (Cases_on ‘n’ >> fs[] >> rfs[] >>
      rename [‘bnf (steps n0 (THE (noreduct M0)))’] >>
      simp[normal_orderTheory.noreduct_thm] >>
      Cases_on ‘noreduct M0’ >> simp[] >- fs[normal_orderTheory.noreduct_bnf] >>
      first_x_assum irule >> fs[] >> qx_gen_tac ‘j’ >>
      first_x_assum (qspec_then ‘SUC j’ mp_tac) >> simp[]) >>
  Cases_on ‘n’ >> fs[] >> rfs[]
  >- (simp[normal_orderTheory.noreduct_thm] >>
      Cases_on ‘noreduct N0’ >> simp[]
      >- fs[normal_orderTheory.noreduct_bnf] >>
      Cases_on ‘m = 0’ >> rw[] >>
      first_x_assum (qspec_then ‘0’ (irule o SIMP_RULE (srw_ss()) [])) >>
      simp[]) >>
  rename [‘n < m’] >>
  ‘¬bnf M0’
    by (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[]) >>
  fs[] >> Cases_on ‘noreduct M0’ >> simp[]
  >- fs[normal_orderTheory.noreduct_bnf] >>
  simp[normal_orderTheory.noreduct_thm] >> first_x_assum irule >> fs[] >>
  qx_gen_tac ‘j’ >> first_x_assum (qspec_then ‘SUC j’ mp_tac) >> simp[]
QED

Theorem bnf_of_VARAPP2:
  bnf_of (VAR s @@ M0 @@ N0) =
  do M <- bnf_of M0; N <- bnf_of N0; SOME (VAR s @@ M @@ N) od
Proof
  Cases_on ‘bnf_of M0’ >> simp[]
  >- (fs[numsAsCompStatesTheory.bnf_of_EQ_NONE_steps] >>
      gen_tac >> pop_assum mp_tac >> map_every qid_spec_tac [‘M0’, ‘n’] >>
      Induct >> simp[] >- (gen_tac >> disch_then (qspec_then ‘0’ mp_tac) >>
                           simp[]) >>
      gen_tac >> strip_tac >>
      first_assum (qspec_then ‘0’ (mp_tac o SIMP_RULE (srw_ss()) [])) >>
      simp[] >> strip_tac >> simp[normal_orderTheory.noreduct_thm] >>
      Cases_on ‘noreduct M0’ >> simp[] >> fs[normal_orderTheory.noreduct_bnf]>>
      first_x_assum match_mp_tac >> gen_tac >>
      first_x_assum (qspec_then ‘SUC n’ mp_tac) >> simp[]) >>
  Cases_on ‘bnf_of N0’ >> simp[]
  >- (fs[numsAsCompStatesTheory.bnf_of_EQ_NONE_steps, stepsTheory.bnf_steps] >>
      ‘∃n0. bnf (steps n0 M0) ∧ ∀i. i < n0 ⇒ ¬bnf (steps i M0)’
        by (qspec_then ‘λj. bnf (steps j M0)’ (irule o BETA_RULE) WOP >>
            metis_tac[]) >>
      qx_gen_tac‘m’ >> Cases_on ‘m ≤ n0’
      >- (qspecl_then [‘m’, ‘n0’, ‘M0’] mp_tac steps_VARAPP2a >> simp[] >>
          metis_tac[stepsTheory.steps_def]) >>
      qspecl_then [‘m’, ‘n0’, ‘M0’] mp_tac steps_VARAPP2b >> simp[]) >>
  fs[stepsTheory.bnf_steps] >>
  rename [‘VAR s @@ M0 @@ N0’, ‘steps n1 M0 = M’, ‘steps n2 N0 = N’] >>
  ‘∃n0. bnf (steps n0 M0) ∧ ∀i. i < n0 ⇒ ¬bnf (steps i M0)’
    by (qspec_then ‘λj. bnf (steps j M0)’ (irule o BETA_RULE) WOP >>
        metis_tac[]) >>
  ‘steps n0 M0 = M’
    by (Cases_on ‘n0 = n1’ >> fs[] >>
        ‘n0 < n1’ by metis_tac[DECIDE “x < y ∨ x = y ∨ y < x:num”] >>
        metis_tac[stepsTheory.bnf_steps_upwards_closed]) >>
  qexists_tac ‘n0 + n2’ >>
  Cases_on ‘n2 = 0’
  >- (qspecl_then [‘n0’, ‘n0’, ‘M0’] mp_tac steps_VARAPP2a >> simp[] >> fs[]) >>
  qspecl_then [‘n0 + n2’, ‘n0’, ‘M0’] mp_tac steps_VARAPP2b >> simp[]
QED

Theorem S_eq_K:
  ¬(S == K)
Proof
  simp[chap3Theory.lameq_betaconversion] >> strip_tac>>
  `∃Z. reduction beta S Z /\ reduction beta K Z`
    by PROVE_TAC [chap3Theory.theorem3_13, chap3Theory.beta_CR] THEN
  ‘normal_form beta S ∧ normal_form beta K’
    by PROVE_TAC [chap2Theory.S_beta_normal, chap2Theory.K_beta_normal,
                  chap3Theory.beta_normal_form_bnf] THEN
  `S = K` by PROVE_TAC [chap3Theory.corollary3_2_1] THEN
  fs[chap2Theory.S_def, chap2Theory.K_def]
QED

Theorem cnil_cvcons:
  ¬(cnil == cvcons h t)
Proof
  strip_tac >>
  ‘cnil @@ S @@ (K @@ (K @@ K)) == cvcons h t @@ S @@ (K @@ (K @@ K))’
    by metis_tac[chap2Theory.lameq_rules] >>
  pop_assum mp_tac >>
  simp_tac (bsrw_ss()) [cnil_def, wh_cvcons, S_eq_K]
QED

Definition ctl0_def:
  ctl0 =
  LAM "l" (
    VAR "l" @@ (cpair @@ cnil @@ cnil)
            @@ LAM "h" (
                 LAM "r" (
                   cpair @@ (csnd @@ VAR "r")
                         @@ (ccons @@ VAR "h" @@ (csnd @@ VAR "r"))
                 )
               )
  )
End

Theorem FV_ctl0[simp]:
  FV ctl0 = ∅
Proof
  simp[ctl0_def, EXTENSION]
QED

Triviality ctl0_eqn = brackabs.brackabs_equiv [] ctl0_def

Theorem ctl0_behaviour:
  ctl0 @@ cnil == cvpr cnil cnil ∧
  ctl0 @@ (ccons @@ h @@ t) == cpair @@ (csnd @@ (ctl0 @@ t)) @@
                                    (ccons @@ h @@ (csnd @@ (ctl0 @@ t))) ∧
  ctl0 @@ cvcons h t == cpair @@ (csnd @@ (ctl0 @@ t)) @@
                             (ccons @@ h @@ (csnd @@ (ctl0 @@ t)))
Proof
  simp_tac (bsrw_ss()) [ctl0_eqn, cnil_def, wh_ccons, wh_cvcons ] >>
  simp_tac (bsrw_ss()) [churchpairTheory.cpair_behaviour]
QED

Theorem ctl0_thm:
  ∀t. ctl0 @@ cvlist t == cvpr (cvlist (TL t)) (cvlist t)
Proof
  Induct_on ‘t’ >>
  asm_simp_tac (bsrw_ss()) [ctl0_behaviour, wh_ccons,
                            churchpairTheory.cpair_behaviour]
QED

Definition ctl_def:
  ctl = B @@ cfst @@ ctl0
End

Theorem FV_ctl[simp]:
  FV ctl = ∅
Proof
  simp[ctl_def]
QED

Theorem ctl_thm:
  ctl @@ cvlist ts == cvlist (TL ts) ∧
  ctl @@ cvcons h (cvlist ts) == cvlist ts
Proof
  simp_tac (bsrw_ss()) [ctl_def, ctl0_thm] >>
  ‘cvcons h (cvlist ts) = cvlist (h::ts)’ by simp[] >> pop_assum SUBST1_TAC >>
  simp_tac (bsrw_ss()) [ctl0_thm, Excl "cvlist_thm"]
QED

Triviality cvlist_LIST_REL:
  ∀l1 l2. cvlist l1 == cvlist l2 <=> LIST_REL $== l1 l2
Proof
  simp[EQ_IMP_THM, cvlist_LIST_REL_cong] >>
  Induct >> simp[]
  >- (Cases >> simp[] >> strip_tac >>
      drule normal_orderTheory.lameq_bnf_of_cong >>
      fs[cnil_cvcons]) >>
  rpt gen_tac >> Cases_on ‘l2’ >> simp[]
  >- metis_tac[chap2Theory.lameq_rules, cnil_cvcons] >>
  strip_tac >>
  rename [‘cvcons h1 (cvlist t1) == cvcons h2 (cvlist t2)’] >>
  ‘cvcons h1 (cvlist t1) @@ S @@ K == cvcons h2 (cvlist t2) @@ S @@ K’
    by metis_tac[chap2Theory.lameq_rules] >>
  full_simp_tac (bsrw_ss()) [wh_cvcons] >> first_x_assum irule >>
  ‘ctl @@ cvcons h1 (cvlist t1) == ctl @@ cvcons h2 (cvlist t2)’
     by asm_simp_tac (bsrw_ss()) [] >>
  pop_assum mp_tac >> simp_tac(bsrw_ss()) [ctl_thm]
QED

Theorem calc_fn_alist_behaviour:
  calc_fn_alist @@ church (dBnum (fromTerm t)) @@ church s ==
  cvlist (
    MAP
      (λ(i,t). cvpr (church i) (church (force_num t)))
      (FILTER (bnf o SND) (GENLIST (λi. (i, steps s (t @@ church i))) s))
  )
Proof
  SIMP_TAC (bsrw_ss()) [calc_fn_alist_eqn, ctabulate_cvlist,
                        Cong cvlist_genlist_cong, csteps_behaviour,
                        churchpairTheory.cpair_behaviour,
                        cfilter_cvlist, cbnf_behaviour, PULL_EXISTS,
                        MEM_GENLIST, cmap_cvlist
                       ] >>
  qmatch_abbrev_tac ‘
    cvlist (MAP f1 (FILTER P1 (GENLIST g1 s))) ==
    cvlist (MAP f2 (FILTER P2 (GENLIST g2 s)))
  ’ >>
  qid_spec_tac ‘s’ >> Induct >>
  simp[GENLIST, rich_listTheory.FILTER_SNOC] >>
  markerLib.UNABBREV_ALL_TAC >>
  simp_tac (bsrw_ss()) [churchpairTheory.csnd_cvpr, cbnf_behaviour] >>
  rw[MAP_SNOC] >> fs[cvlist_LIST_REL, LIST_REL_SNOC] >>
  simp_tac (bsrw_ss()) [churchpairTheory.cpair_behaviour]
QED

(* cn2bl0 0 n = 0 /\
   cn2bl0 (SUC m) n = if n = SUC m then
                        EVEN n :: cn2bl0 m ((n - 1) DIV 2)
                      else cn2bl0 m n
*)
Definition cn2bl0_def:
  cn2bl0 =
  natrec
    @@ (LAM "n" cnil)
    @@ (LAM "m" (LAM "r" (LAM "n" (
         ceqnat @@ VAR "n" @@ (csuc @@ VAR "m")
                @@ (ccons @@ (cis_zero @@ (cmod @@ VAR "n" @@ church 2))
                          @@ (VAR "r" @@
                               (cdiv @@ (cpred @@ VAR "n") @@ church 2)))
                @@ (VAR "r" @@ VAR "n")))))
End

Theorem FV_cn2bl0[simp]:
  FV cn2bl0 = ∅
Proof
  simp[EXTENSION, cn2bl0_def]
QED

Triviality cn2bl0_eqn = brackabs.brackabs_equiv [] cn2bl0_def

Theorem cn2bl0_thm:
  ∀t n.
     n ≤ t ⇒
     cn2bl0 @@ church t @@ church n == cvlist (MAP cB (n2bl n))
Proof
  simp_tac (bsrw_ss()) [cn2bl0_eqn] >>
  Induct >> asm_simp_tac (bsrw_ss()) [churchnumTheory.natrec_behaviour] >>
  qx_gen_tac ‘n’ >> strip_tac >> Cases_on ‘n = SUC t’ >>
  asm_simp_tac (bsrw_ss() ++ ARITH_ss)
               [churchboolTheory.cB_behaviour, DIV_LESS_EQ] >>
  simp[Once num_to_bool_list_def, SimpR “$==”] >>
  simp[EVEN_MOD2] >>
  Cases_on ‘SUC t MOD 2 = 0’ >> simp[]
  >- (‘(SUC t - 2) DIV 2 = t DIV 2’ by intLib.ARITH_TAC >> simp[] >>
      simp_tac (bsrw_ss()) [wh_ccons]) >>
  simp_tac (bsrw_ss()) [wh_ccons]
QED

Definition cn2bl_def:
  cn2bl = S @@ cn2bl0 @@ I
End

Theorem FV_cn2bl[simp]:
  FV cn2bl = ∅
Proof
  simp[cn2bl_def, EXTENSION]
QED

Theorem cn2bl_thm:
  cn2bl @@ church n == cvlist (MAP cB (n2bl n))
Proof
  simp_tac (bsrw_ss()) [cn2bl_def, cn2bl0_thm]
QED

Definition cbeq_def:
  cbeq = LAM "b1" (LAM "b2" (VAR "b1" @@ VAR "b2" @@ (cnot @@ VAR "b2")))
End

Theorem FV_cbeq[simp]:
  FV cbeq = ∅
Proof
  simp[cbeq_def, EXTENSION]
QED

Triviality cbeq_eqn = brackabs.brackabs_equiv [] cbeq_def

Theorem cbeq_behaviour:
  cbeq @@ cB b1 @@ cB b2 == cB (b1 = b2)
Proof
  simp_tac (bsrw_ss()) [cbeq_eqn] >> Cases_on ‘b1’ >>
  simp_tac (bsrw_ss()) []
QED

val _ = export_betarwt "cbeq_behaviour"

Definition cblprefix_def:
  cblprefix =
  LAM "l1" (
    VAR "l1"
      @@ (LAM "l2" (cB T)) (* nil case *)
      @@ (LAM "h" (LAM "r" (LAM "l2" (
            cnull @@ VAR "l2" @@ cB F
                  @@ (cbeq @@ VAR "h" @@ (chd @@ VAR "l2")
                           @@ (VAR "r" @@ (ctl @@ VAR "l2"))
                           @@ cB F)))))
  )
End

Theorem FV_cblprefix[simp]:
  FV cblprefix = ∅
Proof
  simp[cblprefix_def, EXTENSION]
QED

Triviality cblprefix_eqn = brackabs.brackabs_equiv [] cblprefix_def

Theorem cblprefix_behaviour:
  cblprefix @@ cnil @@ t == cB T ∧
  cblprefix @@ cvcons b1t tt1 @@ cnil == cB F ∧
  cblprefix @@ cvcons (cB b1) (cvlist t1) @@ cvcons (cB b2) (cvlist t2) ==
    if b1 = b2 then cblprefix @@ cvlist t1 @@ cvlist t2 else cB F
Proof
  simp_tac (bsrw_ss()) [cblprefix_eqn, wh_cvcons, cnull_def, cnil_def,
                        ctl_thm, wh_chd] >> rw[] >>
  simp_tac (bsrw_ss()) [cblprefix_eqn, cnull_def]
QED

Theorem cblprefix_thm:
  cblprefix @@ cvlist (MAP cB bs1) @@ cvlist (MAP cB bs2) == cB (bs1 ≼ bs2)
Proof
  map_every qid_spec_tac [‘bs2’, ‘bs1’] >> Induct >>
  simp_tac (bsrw_ss()) [cblprefix_behaviour] >>
  Cases_on ‘bs2’ >> simp_tac (bsrw_ss()) [cblprefix_behaviour] >> rw[]
QED

Definition cevery_def:
  cevery =
  LAM "P" (LAM "l"
    (VAR "l" @@ cB T
             @@ (LAM "e" (LAM "r" (VAR "r" @@ (VAR "P" @@ VAR "e") @@ cB F)))))
End

Theorem FV_cevery[simp]:
  FV cevery = ∅
Proof
  simp[cevery_def, EXTENSION]
QED

Triviality cevery_eqn = brackabs.brackabs_equiv [] cevery_def

Theorem cevery_behaviour:
  cevery @@ P @@ cnil == cB T ∧
  cevery @@ P @@ cvcons h (cvlist t) ==
    cevery @@ P @@ cvlist t @@ (P @@ h) @@ cB F
Proof
  simp_tac (bsrw_ss()) [cevery_eqn, wh_cvcons, cnil_def]
QED

Theorem cevery_thm:
  (∀e. MEM e l ⇒ ∃b. P @@ e == cB b) ⇒
  cevery @@ P @@ cvlist l == cB (EVERY (λt. P @@ t == cB T) l)
Proof
  Induct_on ‘l’ >> asm_simp_tac(bsrw_ss()) [cevery_behaviour] >> rw[] >>
  ‘∃b. P @@ h == cB b’ by metis_tac[] >> Cases_on ‘b’ >>
  asm_simp_tac (bsrw_ss()) [] >>
  Cases_on ‘EVERY (λt. P @@ t == cB T) l’ >> asm_simp_tac (bsrw_ss()) []
QED

Definition clength_def:
  clength = LAM "l" (VAR "l" @@ church 0 @@ (LAM "h" csuc))
End

Theorem FV_clength[simp]:
  FV clength = ∅
Proof
  simp[EXTENSION,clength_def]
QED

val clength_eqn = brackabs.brackabs_equiv [] clength_def

Theorem clength_behaviour:
  clength @@ cnil == church 0 ∧
  clength @@ (cvcons h (cvlist t)) == csuc @@ (clength @@ cvlist t)
Proof
  simp_tac (bsrw_ss()) [clength_eqn, wh_cvcons, cnil_def]
QED

Theorem clength_thm:
  clength @@ cvlist t == church (LENGTH t)
Proof
  Induct_on ‘t’ >> asm_simp_tac (bsrw_ss()) [clength_behaviour]
QED

Definition cpfree_check_def:
  cpfree_check =
  LAM "bl1" (LAM "bl2" (
    cor @@ (ceqnat @@ (clength @@ VAR "bl1") @@ (clength @@ VAR "bl2"))
        @@ (cand @@
             (cnot @@ (cblprefix @@ VAR "bl1" @@ VAR "bl2")) @@
             (cnot @@ (cblprefix @@ VAR "bl2" @@ VAR "bl1")))
             ))
End

Theorem FV_cpfree_check[simp]:
  FV cpfree_check = ∅
Proof
  simp[cpfree_check_def, EXTENSION]
QED

val cpfree_check_eqn = brackabs.brackabs_equiv [] cpfree_check_def

Theorem cpfree_check_behaviour:
  cpfree_check @@ cvlist (MAP cB bs1) @@ cvlist (MAP cB bs2) ==
  cB (¬(bs1 ≺ bs2) ∧ ¬(bs2 ≺ bs1))
Proof
  simp_tac(bsrw_ss()) [cpfree_check_eqn, clength_thm, cblprefix_thm] >>
  Cases_on ‘LENGTH bs1 = LENGTH bs2’ >> simp[]
  >- (rpt strip_tac >> drule prefix_length_lt >> simp[]) >>
  rw[prefix_def, EQ_IMP_THM] >> metis_tac[]
QED

Definition cpfree_list_def:
  cpfree_list =
  LAM "l" (
    VAR "l" @@ (cpair @@ cnil @@ cB T) @@ (
      LAM "h" (
        LAM "r" (
          cpair @@ (ccons @@ VAR "h" @@ (cfst @@ VAR "r")) @@
          (cand @@ (csnd @@ VAR "r")
                @@ (cevery @@ (cpfree_check @@ VAR "h") @@ (cfst @@ VAR "r")))
        )
      )
    )
  )
End

Theorem FV_cpfree_list[simp]:
  FV cpfree_list = ∅
Proof
  simp[cpfree_list_def, EXTENSION]
QED

val cpfree_list_eqn = brackabs.brackabs_equiv [] cpfree_list_def

val lameq_sym = List.nth(CONJUNCTS chap2Theory.lameq_rules, 2)

val temp =
  CONV_RULE (SIMP_CONV (bsrw_ss()) [])
            (cpfree_list_eqn
                |> MATCH_MP (List.nth(CONJUNCTS chap2Theory.lameq_rules, 4))
                |> Q.SPEC ‘cvlist bls’) |> MATCH_MP lameq_sym

Theorem cpfree_list_behaviour:
  cpfree_list @@ cnil == cvpr cnil (cB T) ∧
  cpfree_list @@ (cvcons bl1 (cvlist bls)) ==
    cvpr (cvcons bl1 (cfst @@ (cpfree_list @@ cvlist bls)))
         (cand @@ (csnd @@ (cpfree_list @@ cvlist bls))
               @@ (cevery @@ (cpfree_check @@ bl1)
                          @@ (cfst @@ (cpfree_list @@ cvlist bls))))
Proof
  conj_tac >-
  simp_tac (bsrw_ss()) [cpfree_list_eqn, cnil_def,
                        churchpairTheory.cpair_behaviour] >>
  irule (List.nth(CONJUNCTS chap2Theory.lameq_rules, 3)) >>
  assume_tac (cpfree_list_eqn
                |> MATCH_MP (List.nth(CONJUNCTS chap2Theory.lameq_rules, 4))
                |> Q.SPEC ‘cvcons bl1 (cvlist bls)’) >>
  goal_assum dxrule >>
  simp_tac (bsrw_ss()) [wh_cvcons, temp] >>
  simp_tac (bsrw_ss()) [wh_ccons] >>
  simp_tac (bsrw_ss()) [churchpairTheory.cpair_behaviour]
QED

Theorem cpfree_list_thm:
  cpfree_list @@ cvlist (MAP cvlist (MAP (MAP cB) bls)) ==
  cvpr (cvlist (MAP cvlist (MAP (MAP cB) bls))) (cB (prefix_free (set bls)))
Proof
  Induct_on ‘bls’ >>
  asm_simp_tac (bsrw_ss()) [cpfree_list_behaviour, Cong cvpr_cong,
                            Cong cvcons_cong] >>
  gen_tac >> irule cvpr_cong >> simp[] >>
  simp_tac (bsrw_ss()) [cevery_thm, cpfree_check_behaviour, MEM_MAP,
                        PULL_EXISTS] >>
  simp_tac (bsrw_ss()) [EVERY_MAP, cpfree_check_behaviour] >>
  simp[prefix_free_def, EVERY_MEM] >> eq_tac
  >- (rw[] >> map_every Cases_on [‘a = h’, ‘b = h’] >> fs[]) >>
  metis_tac[]
QED

Definition pfsearch_def:
  pfsearch =
  LAM "M" (
    LAM "x" (
      LAM "i" (
        LAM "dom" (
          cand @@ (csnd @@ (cpfree_list @@ (cmap @@ cn2bl @@ VAR "dom")))
               @@ (cmem @@ VAR "x" @@ VAR "dom")
        ) @@ (cmap @@ cfst @@ (calc_fn_alist @@ VAR "M" @@ VAR "i"))
      )
    )
  )
End

Theorem FV_pfsearch[simp]:
  FV pfsearch = ∅
Proof
  simp[pfsearch_def, EXTENSION]
QED

val pfsearch_eqn = brackabs.brackabs_equiv [] pfsearch_def

Theorem cvlist_MAP_cong:
  (∀x. f x == g x) ⇒
  cvlist (MAP f l) == cvlist (MAP g l)
Proof
  rw[] >> irule cvlist_LIST_REL_cong >> Induct_on ‘l’ >> simp[]
QED

Theorem cvlist_MAP_cong_UNCURRY:
  l0 = l1 ⇒ (∀x y. MEM (x,y) l1 ⇒ f x y == g x y) ⇒
  cvlist (MAP (UNCURRY f) l0) == cvlist (MAP (UNCURRY g) l1)
Proof
  rw[] >> irule cvlist_LIST_REL_cong >> Induct_on ‘l0’ >>
  simp[pairTheory.FORALL_PROD]
QED

Theorem pfsearch_thm:
  pfsearch @@ church M @@ church x @@ church i ==
  cB (x < i ∧ bnf (steps i (toTerm (numdB M) @@ church x)) ∧
      prefix_free { n2bl j | bnf (steps i (toTerm (numdB M) @@ church j)) ∧
                             j < i })
Proof
  ‘∃db. M = dBnum db’ by metis_tac[enumerationsTheory.dBnumdB] >>
  rw[] >>
  ‘∃t. db = fromTerm t’ by metis_tac[pure_dBTheory.fromtoTerm] >> rw[]>>
  simp_tac (bsrw_ss()) [pfsearch_eqn, calc_fn_alist_behaviour, cmap_cvlist,
                        MAP_MAP_o, pairTheory.o_UNCURRY_R,
                        combinTheory.o_ABS_R] >>
  ‘∀l. cvlist (MAP (λ(i,t).
                    cfst @@ cvpr (church i) (church (force_num t))) l) ==
       cvlist (MAP (λ(i,t). church i) l) ’
    by (gen_tac >> irule cvlist_MAP_cong >>
        simp_tac (bsrw_ss()) [pairTheory.FORALL_PROD]) >>
  ‘∀l. cvlist (MAP (λ(i,t).
                     cn2bl @@ (cfst @@ cvpr (church i) (church (force_num t))))
                   l) ==
       cvlist (MAP (λ(i,t). cvlist (MAP cB (n2bl i))) l) ’
    by (rpt gen_tac >> irule cvlist_MAP_cong >>
        simp_tac (bsrw_ss()) [pairTheory.FORALL_PROD, cn2bl_thm]) >>
  asm_simp_tac (bsrw_ss()) [cmem_cvlist, PULL_EXISTS, MEM_MAP,
                            pairTheory.FORALL_PROD, EXISTS_MAP] >>
  simp[pairTheory.UNCURRY] >>
  simp_tac (bsrw_ss()) [churchnumTheory.ceqnat_behaviour, EXISTS_MEM,
                        MEM_FILTER, pairTheory.EXISTS_PROD, MEM_GENLIST] >>
  rpt (pop_assum (K all_tac)) >>
  ‘∀l. MAP (λ(i,t:term). cvlist (MAP cB (n2bl i)))
               (l:(num # term) list) =
       MAP cvlist (MAP (MAP cB) (MAP (n2bl o FST) l))’
     by (simp[MAP_MAP_o] >> Induct >> simp[pairTheory.FORALL_PROD]) >>
  pop_assum (simp o single) >>
  simp_tac (bsrw_ss())[cpfree_list_thm] >>
  Cases_on ‘x < i’ >> simp[] >>
  Cases_on ‘bnf (steps i (t @@ church x))’ >> simp[] >>
  simp[prefix_free_def, MEM_MAP, PULL_EXISTS, pairTheory.FORALL_PROD,
       MEM_FILTER, MEM_GENLIST]
QED

Definition Upf_def:
  Upf = LAM "Mi" (
     cfindleast
       @@ (pfsearch @@ (cnfst @@ VAR "Mi") @@ (cnsnd @@ VAR "Mi"))
       @@ LAM "stepcount" (UM @@ VAR "Mi")
  )
End

Theorem FV_Upf[simp]:
  FV Upf = ∅
Proof
  simp[Upf_def, EXTENSION]
QED

val Upf_eqn = brackabs.brackabs_equiv [] Upf_def

Definition pfi_def:
  pfi i ⇔ prefix_free { n2bl x | Phi i x <> NONE }
End

Theorem Phi_SOME_lameq:
  Phi M x = SOME res ⇔
  ∃t. toTerm (numdB M) @@ church x == t ∧ bnf t ∧ force_num t = res
Proof
  simp[PhiSOME_UM] >> simp_tac(bsrw_ss()) [UM_def] >> eq_tac
  >- (qmatch_abbrev_tac ‘CBNF_T == church res ⇒ _’ >>
      strip_tac >> ‘CBNF_T -n->* church res’ by asm_simp_tac (bsrw_ss()) [] >>
      qunabbrev_tac ‘CBNF_T’ >> ‘bnf (church res)’ by simp[] >>
      drule_all cbnf_ofk_works2 >>
      simp_tac (bsrw_ss()) [cforce_num_behaviour] >> metis_tac[bnf_of_SOME_lameq])>>
  strip_tac >>
  ‘bnf_of (toTerm (numdB M) @@ church x) = SOME t’
    by metis_tac[bnf_of_SOME_lameq] >>
  drule cbnf_of_works1 >> asm_simp_tac (bsrw_ss()) []
QED

Theorem Phi_EQ_NONE_has_bnf:
  Phi M x = NONE ⇔ ¬has_bnf (toTerm (numdB M) @@ church x)
Proof
  simp[PhiNONE_UM] >> simp[normal_orderTheory.has_bnf_of] >>
  simp_tac (bsrw_ss()) [UM_def] >> eq_tac >> strip_tac
  >- (drule normal_orderTheory.bnf_of_SOME >> strip_tac >>
      drule_all cbnf_ofk_works2 >> simp[PULL_EXISTS]) >>
  drule_all cbnf_of_works1 >>
  simp_tac (bsrw_ss()) [normal_orderTheory.bnf_bnf_of]
QED

Theorem Phi_EQ_NONE_bnf_steps:
  Phi M x = NONE ⇔ ∀n. ¬bnf (steps n (toTerm (numdB M) @@ church x))
Proof
  simp[Phi_EQ_NONE_has_bnf, normal_orderTheory.has_bnf_of] >>
  ‘∀x. (∀N:term. x <> SOME N) ⇔ x = NONE’ by (Cases >> simp[]) >> simp[] >>
  fs[numsAsCompStatesTheory.bnf_of_EQ_NONE_steps]
QED

Theorem Upf_succeeds:
  pfi M ∧ Phi M i = SOME res ⇒ Upf @@ church (M ⊗ i) == church res
Proof
  simp_tac (bsrw_ss()) [Upf_eqn, churchnumTheory.cnfst_behaviour] >>
  strip_tac >>
  drule_then (qx_choose_then ‘res_t’ strip_assume_tac) PhiSOME_cbnf_ofk >>
  first_x_assum (qspec_then ‘cforce_num’ strip_assume_tac) >>
  full_simp_tac (bsrw_ss()) [cforce_num_behaviour] >>
  fs[GSYM chap3Theory.betastar_lameq_bnf,
     GSYM normal_orderTheory.nstar_betastar_bnf] >>
  drule cbnf_ofk_works2 >> simp[] >>
  disch_then (qx_choose_then ‘res_t'’ strip_assume_tac) >>
  fs[stepsTheory.bnf_steps] >> rename [‘steps n _ = toTerm _’] >>
  ‘pfsearch @@ church M @@ church i @@ church (MAX (i+1) n) == cB T’
    by (simp_tac (bsrw_ss()) [pfsearch_thm] >> conj_tac
        >- (‘bnf (steps n (toTerm (numdB M) @@ church i))’ by simp[] >>
            Cases_on ‘n = MAX (i + 1) n’ >> simp[] >- metis_tac[] >>
            ‘n < MAX (i + 1) n’ by fs[MAX_DEF] >>
            drule_all stepsTheory.bnf_steps_upwards_closed >> simp[]) >>
        fs[pfi_def, prefix_free_def, PULL_EXISTS] >>
        qx_genl_tac [‘a’, ‘b’] >>
        disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
        first_x_assum match_mp_tac >> metis_tac[Phi_EQ_NONE_bnf_steps]) >>
  ‘∀j. ∃b. pfsearch @@ church M @@ church i @@ church j == cB b’
    by simp_tac (bsrw_ss()) [pfsearch_thm] >>
  drule_all_then assume_tac churchnumTheory.cfindleast_termI >>
  asm_simp_tac (bsrw_ss()) [] >> fs[PhiSOME_UM] >>
  asm_simp_tac (bsrw_ss()) []
QED

Theorem Upf_fails1:
  Phi M i = NONE ⇒ ¬has_bnf (Upf @@ church (M ⊗ i))
Proof
  rpt strip_tac >> fs[normal_orderTheory.has_bnf_of, PhiNONE_UM] >>
  full_simp_tac (bsrw_ss()) [Upf_eqn, bnf_of_SOME_lameq] >>
  ‘∀j. ∃b. pfsearch @@ church M @@ church i @@ church j == cB b’
    by simp_tac (bsrw_ss()) [pfsearch_thm] >>
  drule_all_then (qx_choose_then ‘res’ strip_assume_tac)
                 churchnumTheory.cfindleast_bnfE >>
  full_simp_tac (bsrw_ss()) [] >>
  metis_tac[lameq_sym]
QED

Theorem Upf_pfree:
  prefix_free { n2bl i | has_bnf (Upf @@ church (M ⊗ i)) }
Proof
  simp[prefix_free_def, PULL_EXISTS] >> qx_genl_tac [‘a’, ‘b’] >>
  simp[normal_orderTheory.has_bnf_of] >>
  simp_tac (bsrw_ss()) [Upf_eqn, bnf_of_SOME_lameq] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then ‘N1’ strip_assume_tac) mp_tac) >>
  ‘∀j. ∃b. pfsearch @@ church M @@ church a @@ church j == cB b’
    by simp_tac (bsrw_ss()) [pfsearch_thm] >>
  drule_all_then (qx_choose_then ‘res1’ strip_assume_tac)
                 churchnumTheory.cfindleast_bnfE >>
  full_simp_tac(bsrw_ss()) [pfsearch_thm] >>
  disch_then (qx_choose_then ‘N2’ strip_assume_tac) >>
  ‘∀j. ∃bl. pfsearch @@ church M @@ church b @@ church j == cB bl’
    by simp_tac (bsrw_ss()) [pfsearch_thm] >>
  drule_all_then (qx_choose_then ‘res2’ strip_assume_tac)
                 churchnumTheory.cfindleast_bnfE >>
  full_simp_tac(bsrw_ss()) [pfsearch_thm] >>
  Cases_on ‘res1 ≤ res2’
  >- (qpat_x_assum ‘prefix_free { n2bl j | _ ∧ j < res2}’ mp_tac >>
      simp[prefix_free_def, PULL_EXISTS] >> disch_then match_mp_tac >>
      simp[] >> Cases_on ‘res1 = res2’ >- metis_tac[] >>
      ‘res1 < res2’ by simp[] >>
      metis_tac[stepsTheory.bnf_steps_upwards_closed]) >>
  ‘res2 < res1’ by simp[] >>
  qpat_x_assum ‘prefix_free { n2bl j | _ ∧ j < res1}’ mp_tac >>
  simp[prefix_free_def, PULL_EXISTS] >> disch_then match_mp_tac >>
  simp[] >> metis_tac[stepsTheory.bnf_steps_upwards_closed]
QED

(* limitMS M s i = M(i) if i < s and M on i terminates in fewer than s steps
     o/wise, it loops
*)
Definition limitMS_def:
  limitMS =
  LAM "M" (
    LAM "s" (
      LAM "i" (
        cless @@ VAR "i" @@ VAR "s" @@ (
          LAM "t" (
            cbnf @@ VAR "t" @@ (cforce_num @@ VAR "t") @@ Ω
          ) @@ (
            csteps @@ VAR "s"
                   @@ (cdAPP @@ (cnumdB @@ VAR "M") @@ (cchurch @@ VAR "i"))
          )
        ) @@ Ω
      )
    )
  )
End

Theorem FV_limitMS[simp]:
  FV limitMS = ∅
Proof
  simp[limitMS_def, EXTENSION]
QED

val limitMS_eqn = brackabs.brackabs_equiv [] limitMS_def

Theorem Omega_NEQ_church[simp]:
  ¬(Ω == church n) ∧ ¬(church n == Ω)
Proof
  metis_tac[normal_orderTheory.bnf_of_Omega, bnf_of_SOME_lameq,
            optionTheory.NOT_NONE_SOME, lameq_sym, churchnumTheory.bnf_church]
QED

Theorem limitMS_termination_behaviour_eqn:
  limitMS @@ church M @@ church s @@ church i == church n ⇔
  ∃t. steps s (toTerm (numdB M) @@ church i) = t ∧ bnf t ∧ force_num t = n ∧ i < s
Proof
  simp_tac (bsrw_ss())[limitMS_eqn, csteps_behaviour, cbnf_behaviour] >>
  Cases_on ‘i < s’ >> asm_simp_tac (bsrw_ss()) [] >>
  Cases_on ‘bnf (steps s (toTerm (numdB M) @@ church i))’ >>
  asm_simp_tac (bsrw_ss()) []
QED

Theorem limitMS_termination_behaviour_I:
  (∃t. steps s (toTerm (numdB M) @@ church i) = t ∧ bnf t ∧ force_num t = n ∧ i < s)
 ⇒
  limitMS @@ church M @@ church s @@ church i == church n
Proof
  metis_tac[limitMS_termination_behaviour_eqn]
QED

Theorem limitMS_loop_behaviour1:
  s ≤ i ⇒ ¬has_bnf (limitMS @@ church M @@ church s @@ church i)
Proof
  simp_tac (bsrw_ss() ++ ARITH_ss)[normal_orderTheory.has_bnf_of, limitMS_eqn]
QED

Theorem limitMS_looop_behaviour2:
  ¬bnf (steps s (toTerm (numdB M) @@ church i)) ⇒
  ¬has_bnf (limitMS @@ church M @@ church s @@ church i)
Proof
  simp_tac (bsrw_ss() ++ ARITH_ss)[normal_orderTheory.has_bnf_of, limitMS_eqn] >>
  Cases_on ‘i < s’ >>
  asm_simp_tac (bsrw_ss() ++ ARITH_ss)[csteps_behaviour, cbnf_behaviour]
QED

Theorem limitMS_thm:
  limitMS @@ church M @@ church s @@ church i ==
  if i < s ∧ bnf (steps s (toTerm (numdB M) @@ church i)) then UM @@ church (M ⊗ i)
  else Ω
Proof
  simp_tac (bsrw_ss()) [limitMS_eqn] >> Cases_on ‘i < s’ >>
  asm_simp_tac (bsrw_ss()) [cbnf_behaviour, csteps_behaviour] >>
  Cases_on ‘bnf (steps s (toTerm (numdB M) @@ church i))’ >>
  asm_simp_tac (bsrw_ss()) [cbnf_behaviour, csteps_behaviour, UM_def] >>
  qabbrev_tac ‘Mi = toTerm (numdB M) @@ church i’ >>
  ‘bnf_of Mi = SOME (steps s Mi)’ by metis_tac[stepsTheory.bnf_steps] >>
  drule cbnf_of_works1 >> simp_tac (bsrw_ss()) [Abbr‘Mi’]
QED

Theorem exists_steps_bnf:
  (∃n. bnf (steps n t)) ⇔ has_bnf t
Proof
  metis_tac[numsAsCompStatesTheory.bnf_of_EQ_NONE_steps,
            normal_orderTheory.bnf_of_NONE]
QED

Theorem Upf_SOME_pfree_exists:
  Upf @@ church (M ⊗ i) == t ∧ bnf t ∧ res = force_num t ⇒
  ∃N. pfi N ∧ Phi N i = SOME res
Proof
  simp_tac (bsrw_ss()) [Upf_eqn] >>
  ‘∀j. ∃b. pfsearch @@ church M @@ church i @@ church j == cB b’
    by simp_tac (bsrw_ss()) [pfsearch_thm] >> strip_tac >>
  drule_all_then (qx_choose_then ‘step_count’ strip_assume_tac)
                 churchnumTheory.cfindleast_bnfE >>
  full_simp_tac (bsrw_ss()) [pfsearch_thm] >>
  qexists_tac ‘dBnum (fromTerm (limitMS @@ church M @@ church step_count))’ >>
  asm_simp_tac (bsrw_ss())[Phi_SOME_lameq, limitMS_thm] >> reverse conj_tac
  >- metis_tac[lameq_sym, churchnumTheory.bnf_church,
               churchnumTheory.force_num_church] >>
  simp[pfi_def, Phi_EQ_NONE_bnf_steps, exists_steps_bnf,
       normal_orderTheory.has_bnf_of] >>
  simp_tac (bsrw_ss()) [limitMS_thm] >> pop_assum (K ALL_TAC) >>
  fs[prefix_free_def, PULL_EXISTS] >> rw[]
QED

Definition Upfi_def:
  Upfi = dBnum (fromTerm Upf)
End

Theorem Upfi_correct1:
  pfi M ⇒ (Phi Upfi (M ⊗ i) = Phi M i)
Proof
  simp[SimpLHS, Phi_def, Upfi_def] >>
  Cases_on ‘Phi M i’
  >- (drule Upf_fails1 >> simp[GSYM normal_orderTheory.bnf_of_NONE]) >>
  strip_tac >> drule_all_then strip_assume_tac Upf_succeeds >>
  asm_simp_tac (bsrw_ss()) [normal_orderTheory.bnf_bnf_of]
QED

Theorem Upfi_pfree:
  prefix_free {n2bl i | Phi Upfi (M ⊗ i) ≠ NONE }
Proof
  ‘∀x. Phi Upfi x ≠ NONE ⇔ has_bnf (Upf @@ church x)’
    suffices_by simp[Upf_pfree] >>
  simp[Phi_EQ_NONE_has_bnf, Upfi_def]
QED

Theorem Upfi_SOME_pfree_exists:
  Phi Upfi (M ⊗ i) = SOME x ⇒ ∃N. pfi N ∧ Phi Upfi (N ⊗ i) = SOME x
Proof
  strip_tac >> csimp[Upfi_correct1] >> irule Upf_SOME_pfree_exists >>
  fs[Phi_SOME_lameq, Upfi_def] >> metis_tac[]
QED

val _ = export_theory();
