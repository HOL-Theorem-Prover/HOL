open HolKernel Parse boolLib bossLib

open arithmeticTheory whileTheory logrootTheory pred_setTheory listTheory
open reductionEval;
open churchoptionTheory churchlistTheory recfunsTheory numsAsCompStatesTheory
     kolmogorov_complexityTheory invarianceResultsTheory boolListsTheory
open churchDBTheory
open recursivefnsTheory primrecfnsTheory prtermTheory
open unary_recfnsTheory
open numsAsCompStatesTheory
open kolmog_incomputableTheory

val _ = new_theory "plain_kolmog_inequalities"
val _ = intLib.deprecate_int()

Definition univ_plmach_def:
  univ_plmach U <=>
     (∀i x y.
        U (pair x (pair i y)) =
        on2bl (Phi (bl2n i) (bl2n (pair x y)))) ∧
     ∀m. (∀i x y. m <> pair x (pair i y)) ==> U m = NONE
End




Theorem univ_plmach_nonempty[simp]:
  univ_plmach U ⇒ ∀x. ∃y. U y = SOME x
Proof
  rw[univ_plmach_def] >>
  ‘recfn (SOME o (K (bl2n x))) 1’ by (irule primrec_recfn >> fs[primrec_rules]) >>
  ‘∃i. ∀y. Phi i y = (SOME o (K (bl2n x))) [y]’ by (irule unary_rec_fns_phi >> fs[]) >>
  qexists_tac ‘pair x (pair (n2bl i) [])’ >>
  simp[on2bl_SOME,pair_def]
QED

Theorem univ_plmach_nonempty'[simp]:
  univ_plmach U ⇒ ∀x. (∀y. U y ≠ SOME x) = F
Proof
  rpt strip_tac >>
  drule_then (qspec_then ‘x’ strip_assume_tac) univ_plmach_nonempty >>
  simp[]
QED


Theorem univ_plmach_pair_nonempty:
   univ_plmach U  ⇒ {p | U (pair y p) = SOME x} ≠ ∅
Proof
  rw[EXTENSION] >>
  ‘∃a. U a = SOME x’ by simp[] >>
  fs[univ_plmach_def] >>
  ‘∃i b c. a = pair b (pair i c)’
    by metis_tac[optionTheory.NOT_NONE_SOME] >>
  rw[] >> rfs[on2bl_SOME] >>

  qexists_tac ‘pair (n2bl (bl2n i o (nblsnd_i ))) ((pair b c))’ >>
  fs[computable_composition_def, on2bl_SOME, PULL_EXISTS,checkbar_i_def,nblsnd_i_def]
QED

Theorem univ_plmach_pair_nonempty'[simp] =
  SIMP_RULE (srw_ss()) [EXTENSION] univ_plmach_pair_nonempty

Definition rUMibl_def:
  rUMibl = recCn recPhi
                [recCn (SOME o (pr1 nblfst))
                       [SOME o proj 0];
                 recCn (SOME o (pr1 nblsnd))
                       [SOME o proj 0]]
End

Theorem rUMibl_correct:
  rUMibl [bl2n (pair a b)] = Phi (bl2n a) (bl2n b)
Proof
  fs[rUMibl_def,rec2_def,recCn_def,nblfst_correct,nblsnd_correct2]
QED

Theorem rec1_pr1:
  SOME o pr1 f = rec1 (SOME o f)
Proof
  simp[FUN_EQ_THM] >> Cases_on‘x’ >> rw[rec1_def,pr1_def]
QED

Theorem rUMibl_recfn:
  recfn rUMibl 1
Proof
  fs[rUMibl_def] >> irule recfnCn >> rw[] >> irule recfnCn >>
  rw[recfn_rules,recfn_nblsnd,recfn_nblfst] >>
  ‘(SOME ∘ pr1 nblfst) = rec1 (SOME o nblfst)’ suffices_by fs[recfn_nblfst] >>
  fs[rec1_pr1]
QED

Theorem rUMibl_index:
  ∃i. ∀x. Phi i x = rUMibl [x]
Proof
  fs[unary_rec_fns_phi,rUMibl_recfn]
QED

Theorem CKC_thm[simp]:
  univ_plmach U ⇒ CKC U x y = MIN_SET {LENGTH p | U (pair y p) = SOME x}
Proof
  simp[CKC_def, cond_core_complexity_def, univ_plmach_pair_nonempty]
QED

Theorem KC_thm[simp]:
  univ_plmach U ⇒ KC U x = MIN_SET {LENGTH p | U p = SOME x}
Proof
  simp[KC_def, core_complexity_def, EXTENSION]
QED

(* Up to here! *)






Theorem primrec_nblconcat[simp]:
  primrec (pr2 nblconcat) 2
Proof
  irule primrec_pr2 >> fs[nblconcat_def] >>
  qexists_tac
  ‘Cn (pr2 $+ )
      [proj 0 ;
       Cn (pr2 $* )
          [proj 1 ;
           Cn (λl. FUNPOW (λx. 2*x ) ((proj 0) l) ((K 1n) l)  )
              [Cn (pr1 ℓ )
                  [proj 0] ] ] ] ’ >> rw[]
  >- (rpt (irule unary_recfnsTheory.primrec_Cn >>
           rw[primrec_pr_mult,primrec_pr_add,primrec_rules,primrec_ell]) >>
      HO_MATCH_MP_TAC primrec_FUNPOW >> rw[]
      >- (irule primrec_pr1 >> qexists_tac‘Cn (pr2 $*) [K 2;proj 0]’ >> simp[primrec_rules])
      >- (‘(λ(l:num list). 1n) = K 1’ suffices_by simp[] >> simp[FUN_EQ_THM] ) >>
      simp_tac (srw_ss()++boolSimps.ETA_ss) [primrec_rules] ) >>
  Q.SPEC_TAC (‘ℓ m’,‘k’) >> Induct >> simp[FUNPOW_SUC,EXP]
QED



Definition nblpair_to_concat_def:
  nblpair_to_concat = recCn (SOME o pr2 nblconcat) [rec1 (SOME o nblfst);SOME o pr1 nblsnd]
End

Theorem recfn_nblpair_to_concat:
  recfn nblpair_to_concat 1
Proof
  simp[nblpair_to_concat_def] >> irule recfnCn >> rw[recfn_nblsnd,recfn_nblfst,primrec_recfn]
QED

Theorem nblpair_to_concat_correct[simp]:
  nblpair_to_concat [bl2n (pair x y)] = SOME (bl2n (x++y))
Proof
  simp[nblpair_to_concat_def,recCn_def,nblfst_correct,nblsnd_correct2]
QED

val nblpc_i_def =  new_specification ("nblpc_i_def",["nblpc_i"],MATCH_MP unary_rec_fns_phi recfn_nblpair_to_concat)


Definition comp_machine_t_def:
  comp_machine_t =
  LAM "ijx" (
    LAM "ij" (
      LAM "i" (
        LAM "j" (
          LAM "x" (
            cbnf_ofk
              @@ (LAM "r" (UM @@ (cnpair @@ (cnfst @@ VAR "ij")
                                         @@ (cforce_num @@ VAR "r"))))
              @@ (cdAPP @@ (cnumdB @@ (cnsnd @@ VAR "ij"))
                        @@ (cchurch @@ VAR "x"))
          ) @@ (cnsnd @@ VAR "ijx")
        ) @@ (cnsnd @@ VAR "ij")
      ) @@ (cnfst @@ VAR "ij")
    ) @@ (cnfst @@ VAR "ijx")
  )
End

Theorem FV_comp_machine_t[simp]:
  FV comp_machine_t = ∅
Proof
  simp[comp_machine_t_def, EXTENSION]
QED

Triviality comp_machine_equiv = brackabs.brackabs_equiv [] comp_machine_t_def

Theorem comp_machine_t_behaviour_good:
  Phi j x = SOME n ∧ Phi i n = SOME r ⇒
  (comp_machine_t @@ church ((i ⊗ j) ⊗ x) == church r)
Proof
  strip_tac >>
  Q.UNDISCH_THEN ‘Phi j x = SOME n’ mp_tac >>
  simp_tac (bsrw_ss()) [comp_machine_equiv, Phi_def] >> strip_tac >>
  drule cbnf_of_works1 >>
  simp[] >> simp_tac (bsrw_ss())[] >> disch_then (K ALL_TAC) >>
  drule PhiSOME_UM_I >> rw[] >> asm_simp_tac(bsrw_ss()) []
QED

Theorem comp_machine_t_behaviour_bad1:
  Phi j x = NONE ⇒
  bnf_of (comp_machine_t @@ church ((i ⊗ j) ⊗ x)) = NONE
Proof
  strip_tac >>
  simp_tac (bsrw_ss()) [comp_machine_equiv] >>
  simp[PhiNONE_cbnf_ofk]
QED

Theorem comp_machine_t_behaviour_bad2:
  Phi j x = SOME n ∧ Phi i n = NONE ⇒
  bnf_of (comp_machine_t @@ church ((i ⊗ j) ⊗ x)) = NONE
Proof
  strip_tac >>
  Q.UNDISCH_THEN ‘Phi j x = SOME n’ mp_tac >>
  simp_tac (bsrw_ss()) [comp_machine_equiv, Phi_def] >> strip_tac >>
  drule cbnf_of_works1 >> simp_tac (bsrw_ss()) [] >> disch_then (K ALL_TAC) >>
  fs[PhiNONE_UM, normal_orderTheory.bnf_of_NONE]
QED

Definition comp_machine_i_def:
  comp_machine_i = dBnum (fromTerm comp_machine_t)
End

Theorem Phi_comp:
  Phi comp_machine_i ((i ⊗ j) ⊗ x) = Phi (i o j) x
Proof
  simp[computable_composition_def] >>
  simp[SimpLHS, Phi_def, comp_machine_i_def] >>
  Cases_on ‘Phi j x’
  >- simp[comp_machine_t_behaviour_bad1] >>
  rename [‘Phi j x = SOME r’] >>
  Cases_on ‘Phi i r’
  >- (drule_all comp_machine_t_behaviour_bad2 >> simp[]) >>
  drule_all comp_machine_t_behaviour_good >>
  asm_simp_tac (bsrw_ss()) [normal_orderTheory.bnf_bnf_of]
QED

Definition comp_machine_bl:
  comp_machine_bl =
    recCn recPhi [
      SOME o K comp_machine_i;
      recCn (SOME o pr2 $*,) [
        recCn (SOME o pr2 $*,) [
          recCn (rec1 (SOME o nblfst)) [
            recCn (rec1 (SOME o nblfst)) [SOME o proj 0]
          ];
          recCn (SOME o pr1 nblsnd) [
            recCn (rec1 (SOME o nblfst)) [SOME o proj 0]
          ]
        ];
        recCn (SOME o pr1 nblsnd) [SOME o proj 0]
      ]
    ]
End

Theorem recfn_comp_machine_bl[simp]:
  recfn comp_machine_bl 1
Proof
  simp[comp_machine_bl] >>
  rpt (irule recfnCn >> simp[recfn_SOMEnpair, recfn_nblsnd, recfn_rules,
                             recfn_nblfst] >> rw[])
QED

Theorem comp_machine_bl_correct:
  comp_machine_bl [bl2n (pair (pair i j) x)] =
  Phi (bl2n i o bl2n j) (bl2n x)
Proof
  simp[comp_machine_bl, recCn_def, Phi_comp]
QED

val comp_bli = new_specification (
  "comp_bli", ["comp_bli"],
  MATCH_MP unary_rec_fns_phi recfn_comp_machine_bl
);

(* takes (pair (pair f (pair g1 g2)) x) and computes f (g1 x) (g2 x)
   as f, g1 and g2 are all indexes, running them actually involves a call
   to recPhi.
*)
Definition nbl_comp2_def:
  nbl_comp2 =
  recCn recPhi [
    recCn (rec1 (SOME o nblfst)) [
      recCn (rec1 (SOME o nblfst)) [SOME o proj 0] (* f is fst(fst arg) *)
    ];
    recCn (SOME o pr2 $*,) [ (* g1 x ⊗  g2 x *)
      recCn recPhi [ (* Phi g1 x *)
        recCn (rec1 (SOME o nblfst)) [
          recCn (SOME o pr1 nblsnd) [
            recCn (rec1 (SOME o nblfst)) [SOME o proj 0]
          ]
        ];
        recCn (SOME o pr1 nblsnd) [SOME o proj 0] (* x is snd (arg) *)
      ];
      recCn recPhi [ (* Phi g2 x *)
        recCn (SOME o pr1 nblsnd) [
          recCn (SOME o pr1 nblsnd) [
            recCn (rec1 (SOME o nblfst)) [SOME o proj 0]
          ]
        ];
        recCn (SOME o pr1 nblsnd) [SOME o proj 0] (* x is snd (arg) *)
      ]
    ]
  ]
End

Theorem recfn_nbl_comp2:
  recfn nbl_comp2 1
Proof
  simp[nbl_comp2_def] >>
  rpt (irule recfnCn >> simp[recfn_SOMEnpair, recfn_nblsnd, recfn_rules,
                             recfn_nblfst] >> rw[])
QED

Theorem nbl_comp2_correct:
  nbl_comp2 [bl2n (pair (pair f (pair g1 g2)) x)] =
  do
    r1 <- Phi (bl2n g1) (bl2n x);
    r2 <- Phi (bl2n g2) (bl2n x);
    Phi (bl2n f) (r1 ⊗ r2);
  od
Proof
  simp[nbl_comp2_def, recCn_def] >>
  Cases_on ‘Phi (bl2n g1) (bl2n x)’ >> simp[] >>
  Cases_on ‘Phi (bl2n g2) (bl2n x)’ >> simp[]
QED

val nbl_comp2_i_def =
new_specification ("nbl_comp2_i_def", ["nbl_comp2_i"],
                   MATCH_MP unary_rec_fns_phi recfn_nbl_comp2)











Definition nblpair_def:
  nblpair = Cn (pr2 nblconcat)
               [Cn (pr2 nblconcat)
                   [Cn (pr2 nblconcat)
                       [Cn nblTpow
                           [Cn (pr1 (λp. ℓ p))
                               [proj 0]];
                        K 1];
                    proj 0];
                proj 1]
End



Theorem primrec_nblpair:
  primrec nblpair 2
Proof
  simp[nblpair_def] >> rpt (irule primrec_Cn >> rw[primrec_rules,primrec_nblconcat,primrec_nblTpow,primrec_ell])
QED

Theorem nblconcat_correct2:
  nblconcat a b = bl2n ((n2bl a)++(n2bl b))
Proof
  ‘∃x. a = bl2n x ∧ ∃y. b=bl2n y’ by (qexists_tac‘n2bl a’ >> rw[] >> qexists_tac‘n2bl b’ >> rw[]) >>  fs[nblconcat_correct]
QED





Theorem nblpair_correct:
  nblpair [x;y] = bl2n (pair (n2bl x) (n2bl y))
Proof
  rw[nblpair_def,nblconcat_correct2,pair_def,bar_def,nblTpow_correct] >>
  simp[Once num_to_bool_list_def]
QED

Definition nblpair_flip_def:
  nblpair_flip = recCn (SOME o nblpair) [SOME o pr1 nblsnd;rec1 (SOME o nblfst)]
End



Theorem recfn_nblpair_flip:
  recfn nblpair_flip 1
Proof
  simp[nblpair_flip_def] >> irule recfnCn >> rw[recfn_nblsnd,recfn_nblfst,primrec_recfn] >>
  irule primrec_recfn >> simp[primrec_nblpair]
QED

Theorem nblpair_flip_correct[simp]:
  nblpair_flip [bl2n (pair x y)] = SOME (bl2n (pair y x))
Proof
  simp[nblpair_flip_def,recCn_def,nblfst_correct,nblsnd_correct2,nblpair_correct]
QED

val nblpf_i_def =  new_specification ("nblpf_i_def",["nblpf_i"],MATCH_MP unary_rec_fns_phi recfn_nblpair_flip)



val nblpair_i_def = new_specification(
  "nblpair_i_def", ["nblpair_i"],
  MATCH_MP binary_rec_fns_phi (MATCH_MP primrec_recfn primrec_nblpair)
     |> SIMP_RULE (srw_ss()) [nblpair_correct]
);

Overload rfst = “rec1 (SOME o nblfst)”
Overload rsnd = “SOME o pr1 nblsnd”
Overload rpair = “SOME o nblpair”


Definition extra_info_cond_prog_def:
   extra_info_cond_prog = (* f ((y,z),(a,b)) = U(y,(a,b)) = Phi a (y,b)  *)
   recCn recPhi [recCn rfst [recCn rsnd [SOME o proj 0]];
                recCn rpair [recCn rfst [recCn rfst [SOME o proj 0]];
                             recCn rsnd [recCn rsnd [SOME o proj 0] ]] ]
End

Theorem recfn_extra_info_cond_prog:
  recfn extra_info_cond_prog 1
Proof
  simp[extra_info_cond_prog_def] >>
  rpt (irule recfnCn >> simp[recfn_SOMEnpair, recfn_nblsnd, recfn_rules,
                             recfn_nblfst, primrec_recfn, primrec_nblpair] >>
       rw[])
QED

Theorem extra_info_cond_prog_correct:
  extra_info_cond_prog [bl2n (pair (pair y z) (pair a b))] =
  Phi (bl2n a) (bl2n (pair y  b))
Proof
  simp[extra_info_cond_prog_def, recCn_def, nblpair_correct]
QED



Definition subaddprog_def:
  subaddprog = (* f (a,b,c,u,v) =  pair(b(a,c), u(b(a,c), v))*)
  let bac =
        recCn recPhi [
          recCn rfst [recCn rsnd [SOME o proj 0]]; (* b *)
          recCn rpair [
            (* a *) recCn rfst [SOME o proj 0];
            (* c *) recCn rfst [recCn rsnd [recCn rsnd [SOME o proj 0]]]
          ]
        ]
  in
    recCn rpair [
      bac;
      recCn recPhi [
        recCn rfst [recCn rsnd [recCn rsnd [recCn rsnd [SOME o proj 0]]]];(*u*)
        recCn rpair [
          bac;
          recCn rsnd [recCn rsnd [recCn rsnd [recCn rsnd [SOME o proj 0]]]](*v*)
        ]
      ]
    ]
End

Theorem recfn_subaddproj:
  recfn subaddprog 1
Proof
  simp[subaddprog_def] >>
  rpt (irule recfnCn >> simp[recfn_SOMEnpair, recfn_nblsnd, recfn_rules,
                             recfn_nblfst, primrec_recfn, primrec_nblpair] >>
       rw[])
QED

Theorem subaddprog_correct:
  subaddprog [bl2n (pair a (pair b (pair c (pair u v))))] =
  do
    x <- Phi (bl2n b) (bl2n (pair a c)) ;
    y <- Phi (bl2n u) (bl2n (pair (n2bl x) v)) ;
    SOME (bl2n (pair (n2bl x) (n2bl y)))
  od
Proof
  simp[subaddprog_def, recCn_def, nblpair_correct] >>
  Cases_on ‘Phi (bl2n b) (bl2n (pair a c))’ >> simp[] >>
  Cases_on ‘Phi (bl2n u) (bl2n (pair (n2bl x) v))’ >> simp[]
QED


Definition SIb_machine_def:
  SIb_machine =
  let len = recCn rfst [SOME o proj 0];
      aibjc = recCn rsnd [SOME o proj 0];
      aib = recCn (rec2 (λx y. SOME (nblft x y))) [aibjc;len];
      jc = recCn (SOME o pr_nblsr) [len;aibjc];
      a = recCn rfst [aib];
      i = recCn rfst [recCn rsnd [aib]];
      b = recCn rsnd [recCn rsnd [aib]];
      j = recCn rfst [jc];
      c = recCn rsnd [jc];
      x = recCn recPhi [i; recCn rpair [a;b]];
      y = recCn recPhi [j;recCn rpair [recCn rpair [x;len];c] ]
  in
    recCn rpair [y;x]
End

Theorem nblsr_thm = DROP_n2bl |> GSYM |> SPEC_ALL |> AP_TERM “bl2n” |> REWRITE_RULE [bool_num_inv];

Theorem nblft_thm = TAKE_n2bl |> GSYM |> SPEC_ALL |> AP_TERM “bl2n” |> REWRITE_RULE [bool_num_inv]

Theorem SIb_machine_correct:
  len = n2bl (LENGTH (pair a (pair i b) )) ==>
  SIb_machine [bl2n (pair len ((pair a (pair i b) ) ++ (pair j c) ) )] =
  do
    x <- Phi (bl2n i) (bl2n (pair a b));
    y <- Phi (bl2n j) (bl2n (pair (pair (n2bl x) len) c));
    SOME (bl2n (pair (n2bl y) (n2bl x)))
  od
Proof
  strip_tac >>
  fs[SIb_machine_def,recCn_def,pr_nblsr_correct,nblsr_thm,nblft_thm,
     rich_listTheory.DROP_LENGTH_APPEND,rich_listTheory.TAKE_LENGTH_APPEND,
     nblpair_correct,Excl "pair_LENGTH"] >>
  Cases_on‘ Phi (bl2n i) (bl2n (pair a b))’ >> simp[Excl "pair_LENGTH"] >>
  Cases_on‘
    Phi (bl2n j)
        (bl2n
         (pair (pair (n2bl x) (n2bl (LENGTH (pair a (pair i b))))) c))’ >>
  simp[Excl "pair_LENGTH"]
QED

Theorem recfn_nblft:
 recfn (rec2 (λx y. SOME (nblft x y))) 2
Proof
  simp[nblft_phi_lem] >>
  rpt (irule recfnCn >> simp[recfn_SOMEnpair, recfn_nblsnd, recfn_rules,recfn_some_num,
                             recfn_nblfst, primrec_recfn, primrec_nblpair,recfn_pr_nblsr] >>
       rw[])
QED

Theorem recfn_SIb_machine:
  recfn SIb_machine 1
Proof
  simp[SIb_machine_def] >>
  rpt (irule recfnCn >> simp[recfn_SOMEnpair, recfn_nblsnd, recfn_rules,recfn_nblft,
                             recfn_nblfst, primrec_recfn, primrec_nblpair,recfn_pr_nblsr] >>
       rw[])
QED


Definition nblbar_def:
  nblbar = Cn (pr2 nblconcat) [Cn nblTpow [Cn (pr1 (λp. ℓ p)) [proj 0]];
                               Cn (pr2 nblconcat) [K 1;proj 0] ]
End

Theorem nblconcat_thm:
  nblconcat a b = bl2n (n2bl a ++ n2bl b)
Proof
  ‘∃m. a = bl2n m’ by (qexists_tac‘n2bl a’ >> fs[]) >>
  ‘∃n. b = bl2n n’ by (qexists_tac‘n2bl b’ >> fs[]) >>
  rw[]
QED

Theorem nblbar_correct:
  nblbar [l] = bl2n (bar (n2bl l))
Proof
  simp[nblbar_def,nblconcat_thm,nblTpow_correct,bar_def] >> EVAL_TAC
QED

Theorem primrec_nblbar:
  primrec nblbar 1
Proof
  fs[nblbar_def] >>
  rpt (irule primrec_Cn >> rw[primrec_nblconcat,primrec_nblTpow,primrec_ell,primrec_rules])
QED





(* up to here *)


Theorem extra_information1:
  univ_plmach U ==> ∃c. ∀x y. (CKC U x y) <= (KC U x) + c
Proof
  rw[] >>
  qx_choose_then ‘rUMi’ strip_assume_tac rUMibl_index >>
  qabbrev_tac‘j = rUMi o nblsnd_i’ >>
  qexists_tac‘2 * ℓ j + 1’ >> rw[] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >>
  rw[EXTENSION, SIMP_RULE (srw_ss()) [EXTENSION] univ_plmach_pair_nonempty] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >> fs[PULL_EXISTS] >>
  rename [‘univ_plmach U’, ‘U p2 = SOME x’] >>
  fs[univ_plmach_def] >>
  ‘∃a i b. p2 = pair a (pair i b)’
     by metis_tac[optionTheory.NOT_SOME_NONE] >> rw[] >>
  qabbrev_tac ‘ARG2 = pair (n2bl j) (pair i (pair a b))’ >>
  ‘U (pair y ARG2) = SOME x’
    by (rfs[Abbr‘ARG2’, Abbr‘j’, computable_composition_def, rUMibl_correct,on2bl_SOME,nblsnd_i_def] )>>
  last_x_assum drule >> simp[Abbr‘ARG2’, LEFT_ADD_DISTRIB]
QED

Theorem subadditivity1:
  univ_plmach U ==> ∃c. ∀x y. KC U (x++y) <= KC U (pair x y) + c
Proof
  rw[] >>
  assume_tac nblpc_i_def >>
  qexists_tac‘4 * ℓ nblpc_i + 2 * ℓ comp_bli + 3’ >>
  rw[] >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >> fs[PULL_EXISTS] >>
  rename[‘U pp = SOME (pair x y)’] >> fs[univ_plmach_def] >>
  ‘∃pi a b. pp = pair a (pair pi b)’
    by metis_tac[optionTheory.NOT_SOME_NONE] >>
  rw[] >> rfs[on2bl_SOME] >>
  qabbrev_tac ‘
    ARG = pair (pair (n2bl nblpc_i) pi) (pair (n2bl comp_bli) (pair a b))
  ’ >>
  ‘U ARG = SOME (x++y)’
     by (simp[Abbr‘ARG’, comp_bli] >>
         ‘z = bl2n (pair x y)’ by simp[] >>
         rw[comp_machine_bl_correct, on2bl_SOME, computable_composition_def]) >>
  last_x_assum drule >> simp[Abbr‘ARG’]
QED

Theorem extra_information2:
  univ_plmach U ⇒ ∃c. ∀x y. KC U x ≤ KC U (pair x y) + c
Proof
  rw[] >>
  qexists_tac‘4 * ℓ nblfst_i + 2 * ℓ comp_bli + 5’ >> rw[] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  rename[‘U pp = SOME (pair x y)’] >>
  fs[univ_plmach_def, PULL_EXISTS] >>
  ‘∃a i c. pp = pair a (pair i c)’
      by metis_tac[optionTheory.NOT_SOME_NONE] >> rw[] >> rfs[on2bl_SOME] >>
  qabbrev_tac ‘
    ARG = pair (pair (n2bl nblfst_i) i) (pair (n2bl comp_bli) (pair a c))
  ’ >>
  ‘U ARG = SOME x’ by
    (simp[computable_composition_def, Abbr‘ARG’, comp_bli, on2bl_SOME,
          comp_machine_bl_correct] >>
     ‘z = bl2n (pair x y)’ by simp[] >>
     rw[nblfst_i_def]) >>
  last_x_assum drule >> simp[Abbr‘ARG’, LEFT_ADD_DISTRIB]
QED

Theorem subadditivity3:
  univ_plmach U ==> ∃c. ∀x y. KC U x + CKC U y x <= KC U x + KC U y + c
Proof
  metis_tac[ADD_ASSOC,LE_ADD_LCANCEL, extra_information1]
QED

Theorem symmetry_of_information2a:
  univ_plmach U ==> ∃c. ∀x y. KC U (pair x y) <= KC U (pair y x) + c
Proof
  rw[] >>
  qexists_tac‘4 * ℓ nblpf_i + 2 * ℓ comp_bli + 5’ >> rw[] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  fs[PULL_EXISTS, univ_plmach_def] >>
  rename[‘U pp = SOME (pair y x)’] >>
  ‘∃a i b. pp = pair a (pair i b)’
    by metis_tac[optionTheory.NOT_SOME_NONE] >>
  rw[] >> rfs[on2bl_SOME] >>
  qabbrev_tac ‘
    ARG = pair (pair (n2bl nblpf_i) i) (pair (n2bl comp_bli) (pair a b))
  ’ >>
  ‘U ARG = SOME (pair x y)’
    by (simp[Abbr‘ARG’, comp_bli] >>
        simp[comp_machine_bl_correct,computable_composition_def, nblpf_i_def] >>
        ‘z = bl2n (pair y x)’ by simp[] >> rw[on2bl_def]) >>
  last_x_assum drule >> simp[Abbr‘ARG’]
QED


Theorem extra_information_cond1:
  univ_plmach U ==> ∃c. ∀x y z. CKC U x (pair y z) <= CKC U x y + c
Proof
  rw[] >>
  qx_choose_then ‘exinfoprog_i’ strip_assume_tac
                 (MATCH_MP unary_rec_fns_phi recfn_extra_info_cond_prog) >>
  qexists_tac ‘2 * ℓ exinfoprog_i + 7’ >> rw[] >>

  DEEP_INTRO_TAC MIN_SET_ELIM >>
  rw[EXTENSION, SIMP_RULE (srw_ss()) [EXTENSION] univ_plmach_pair_nonempty] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >>
  rw[EXTENSION, SIMP_RULE (srw_ss()) [EXTENSION] univ_plmach_pair_nonempty] >>
  fs[PULL_EXISTS] >>
  rename [‘U (pair (pair y z) p1) = SOME x’, ‘U (pair y p2) = SOME x’]>>
  fs[univ_plmach_def] >>
  ‘∃a b. p2 = pair a b’
     by metis_tac[optionTheory.NOT_SOME_NONE, pair_11] >>
  rw[] >> rfs[on2bl_SOME] >> rw[] >>

  rename [‘Phi (bl2n a) _ = SOME x’] >>
  qabbrev_tac‘
    ARG = pair (n2bl exinfoprog_i) (pair a b)
  ’ >>
  ‘U (pair (pair y z) ARG) = SOME (n2bl x)’
    by (simp[Abbr‘ARG’, extra_info_cond_prog_correct, on2bl_def] >> fs[]) >>
  last_x_assum drule >> simp[Abbr‘ARG’]
QED




Theorem symmetry_of_information1b:
  univ_plmach U ==>
  ∃c. ∀x y. KC U (pair x y) ≤ CKC U x (pair y (n2bl (KC U y))) + KC U y + 2*(LENGTH y) + c
Proof
  rw[] >>
  qx_choose_then ‘SIb_i’ strip_assume_tac
                 (MATCH_MP unary_rec_fns_phi recfn_SIb_machine) >>
  qexists_tac ‘2 * ℓ SIb_i + 20 + 3 * ℓ (print_index ∘ nblfst_i)’ >> rw[] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >>
  rw[EXTENSION, SIMP_RULE (srw_ss()) [EXTENSION] univ_plmach_pair_nonempty] >>
  fs[PULL_EXISTS, univ_plmach_def] >>
  rename [‘U p = SOME (pair x y)’, ‘U p1 = SOME y’,
          ‘U (pair (pair y (n2bl (LENGTH p1))) p2) = SOME x’] >>
  ‘∃a1 i1 b1. p1 = pair a1 (pair i1 b1)’
    by metis_tac[optionTheory.NOT_SOME_NONE] >>
  rw[] >> rfs[on2bl_SOME, Excl "pair_LENGTH"] >> rw[] >>
  qabbrev_tac ‘N1 = LENGTH (pair a1 (pair i1 b1))’ >>
  ‘∃i2 b2. p2 = pair i2 b2’
     by metis_tac[optionTheory.NOT_SOME_NONE, pair_11] >>
  rw[] >> rfs[on2bl_SOME, Excl "pair_LENGTH"] >> rw[] >>
  rename [‘U p = SOME (pair (n2bl x) (n2bl y))’] >>
  qabbrev_tac‘ARG = pair (n2bl N1) (pair (n2bl SIb_i) (pair a1 (pair i1 b1) ++ pair i2 b2))’ >>
  ‘U ARG = SOME (pair (n2bl x) (n2bl y))’ by (simp[Abbr‘ARG’,SIb_machine_correct,on2bl_SOME]) >>
  qmatch_abbrev_tac‘LENGTH p <= RR’ >> ‘LENGTH ARG <= RR’ suffices_by metis_tac[LESS_EQ_TRANS] >>
  simp[Abbr‘ARG’,Abbr‘RR’,Abbr‘N1’,pair_LENGTH] >>
  ‘U (pair (n2bl y) (pair (n2bl (print_index o nblfst_i)) [] )) = SOME (n2bl y)’ by
    (simp[computable_composition_def,on2bl_SOME,nblfst_i_def,print_index_correct]) >>
  ‘LENGTH (pair a1 (pair i1 b1))  ≤ LENGTH (pair (n2bl y) (pair (n2bl (print_index ∘ nblfst_i)) []))’
    by metis_tac[] >> fs[pair_LENGTH] >>
  ‘2 * LENGTH a1 + (LENGTH b1 + (2 * LENGTH i1 + 2)) + 10 ≤
        2 * ℓ y + (2 * ℓ (print_index ∘ nblfst_i) + 2) + 10’ by fs[] >>
  ‘2 * ℓ (2 * LENGTH a1 + (LENGTH b1 + (2 * LENGTH i1 + 2))) + 5 <= 2 * LENGTH a1 + (LENGTH b1 + (2 * LENGTH i1 + 2)) + 10 ∧ 2 * ℓ y + (2 * ℓ (print_index ∘ nblfst_i) + 2) + 10 <= 2 * ℓ y + (3 * ℓ (print_index ∘ nblfst_i) + 23)’ suffices_by metis_tac[LESS_EQ_TRANS] >> rw[] >>
  ‘2 * ℓ (2 * LENGTH a1 + (LENGTH b1 + (2 * LENGTH i1 + 2))) + 5 ≤
        2 * LENGTH a1 + (LENGTH b1 + (2 * LENGTH i1 + 2)) + 5 + 3’ suffices_by fs[] >>
  qabbrev_tac‘abi = 2 * LENGTH a1 + (LENGTH b1 + (2 * LENGTH i1 + 2))’ >> fs[] >>
  rpt (pop_assum kall_tac) >>
  ‘2 * ℓ abi <= abi + 3’ suffices_by simp[] >>
  ‘2 ** ℓ abi <= abi + 1’ by fs[exp_ELL1] >>
  ‘2 * ℓ abi <= 2 ** ℓ abi + 2’ suffices_by fs[] >> pop_assum kall_tac >>
  qabbrev_tac‘n = ℓ abi’ >>pop_assum kall_tac >>
  Induct_on‘n’ >> rw[EXP,MULT_SUC] >>
  ‘n < 2 ** n’ by fs[X_LT_EXP_X] >> fs[]
QED




Theorem subadditivity2:
  univ_plmach U ==> ∃c. ∀x y. KC U (pair x y) <= KC U x +  CKC U y x + 2*(LENGTH x) +  c
Proof
  strip_tac >>
  ‘∃c. ∀x y.CKC U y (pair x (n2bl (KC U x))) + KC U x + 2*(LENGTH x)  <=
            KC U x +  CKC U y x + 2*(LENGTH x) +  c’ by
    (assume_tac extra_information_cond1 >>
     ‘∃c. ∀x y z. CKC U x (pair y z) ≤ CKC U x y + c’ by fs[] >>
     qexists_tac‘c’ >> rw[Excl"KC_thm",Excl"CKC_thm"] >>
     ‘CKC U y (pair x (n2bl (KC U x))) ≤ CKC U y x + c’ by metis_tac[] >>
      qmatch_abbrev_tac‘2 * lx + (Kx + CKCUyxK) <= c + (2*xl + (Kx +CKCUxy))’ >> fs[]) >>
  assume_tac symmetry_of_information1b  >>
  ‘∃c1.∀x y.KC U (pair x y) ≤
          CKC U x (pair y (n2bl (KC U y))) + KC U y + 2 * LENGTH y + c1’ by metis_tac[] >>
  assume_tac symmetry_of_information2a >>
  ‘∃c2. ∀x y. KC U (pair x y) ≤ KC U (pair y x) + c2’ by metis_tac[] >>
  qexists_tac‘c+c1+c2’ >> rw[Excl"KC_thm",Excl"CKC_thm"] >>
  ‘CKC U y (pair x (n2bl (KC U x))) + KC U x + 2 * LENGTH x +c1 +c2 ≤
   KC U x + CKC U y x + 2 * LENGTH x + c +c1 +c2’ by metis_tac[LESS_EQ_MONO_ADD_EQ] >>
   ‘KC U (pair y x) +c2≤
            CKC U y (pair x (n2bl (KC U x))) + KC U x + 2 * LENGTH x + c1 + c2’ by
     metis_tac[LESS_EQ_MONO_ADD_EQ] >>
   ‘KC U (pair x y) <= KC U (pair y x) + c2’ by metis_tac[] >>
  fs[LESS_EQ_TRANS,Excl"KC_thm",Excl"CKC_thm"]
QED


Theorem univ_plmach_univ_rf:
  univ_plmach U ==> univ_rf U
Proof
  rw[univ_plmach_def,univ_rf_def] >>
  qexists_tac‘pair [] (pair (n2bl (f o nblsnd_i)) [])’ >> strip_tac >>
  ‘pair [] (pair (n2bl (f ∘ nblsnd_i)) []) ++ n2bl x = pair [] (pair (n2bl (f ∘ nblsnd_i)) ( n2bl x))’ by fs[pair_def] >>
  ‘on2bl (Phi f x) = on2bl (Phi (bl2n (n2bl (f ∘ nblsnd_i))) (bl2n (pair [] (n2bl x))))’ suffices_by
   metis_tac[] >> fs[on2bl_SOME,computable_composition_def,Excl"pair_nil",nblsnd_i_def]
QED

(* Up to here *)

(*

Theorem symmetry_of_information1a:
  univ_plmach U ==>
  ∃c. ∀x y.  CKC U x (pair y (n2bl (KC U y))) + KC U y <= KC U (pair x y) + 2*LENGTH x + c
Proof
  rw[] >>
  qx_choose_then ‘SIb_i’ strip_assume_tac
                 (MATCH_MP unary_rec_fns_phi recfn_SIb_machine) >>
  qexists_tac ‘2 * ℓ SIb_i + 20 + 3 * ℓ (print_index ∘ nblfst_i)’ >> rw[] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[EXTENSION] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >>
  rw[EXTENSION, SIMP_RULE (srw_ss()) [EXTENSION] univ_plmach_pair_nonempty] >>
  fs[PULL_EXISTS, univ_plmach_def] >>
  rename[‘LENGTH p1 + LENGTH p2 <= LENGTH p3 + _’] >>
  (* Maybe not too bad actually
     If the program runs (rsnd o p3) then checks if rfst o rfst is equal to the output, if it isn't then it outputs the output, otherwise output (rfst o p3)
     The problem with this is that we end up with 2*p3+c <= p3+c
  *)
  ‘U (pair (pair y (n2bl (LENGTH p1))) p4) = SOME x ∧ U p5 = SOME y ∧ LENGTH (p4++p5) <= LENGTH p3 + _’
QED

Theorem symmetry_of_information2b:
  univ_mach U ==>
  ∃c. ∀x y.
    CKC U y (pair x (n2bl (KC U x))) + KC U x ≤
    CKC U x (pair y (n2bl (KC U y))) + KC U y + c
Proof
  cheat
QED

*)

val _ = export_theory()
