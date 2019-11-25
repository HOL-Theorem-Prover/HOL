open HolKernel Parse boolLib bossLib
open numsAsCompStatesTheory
open boolListsTheory
open extNatTheory pred_setTheory recfunsTheory prtermTheory recursivefnsTheory primrecfnsTheory

val _ = new_theory "kolmogorov_complexity";


Theorem K_lemma =
    MATCH_MP normal_orderTheory.lameq_bnf_of_cong chap2Theory.lameq_K

Definition prefix_machine_def:
prefix_machine (U:bool list -> bool list option) =
                                ?P. prefix_free P/\(!x. x IN P <=> ?y. U x = SOME y)
End

Definition core_complexity_def:
  core_complexity (U:bool list -> bool list option) x = 
    if  { p | U p = SOME x} = {} then NONE
    else SOME (MIN_SET {LENGTH p | U p = SOME x})
End

Definition KC_def:
  KC U x = THE (core_complexity U x)
End


Definition prefix_kolmog_complexity_def:
prefix_kolmog_complexity U x = if prefix_machine U then core_complexity U x  else NONE
End



Definition cond_core_complexity_def:
  cond_core_complexity U x y =
                       if  { p | U (pair y p) = SOME x} = {} then NONE
                       else SOME (MIN_SET {LENGTH p | U (pair y p) = SOME x})
End

Definition CKC_def:
  CKC U x y = THE (cond_core_complexity U x y)
End

val prefix_rec_fun_def = Define`prefix_rec_fun i = prefix_free (IMAGE n2bl {x|Phi i x <> NONE})`

val pr_log2_def = Define`pr_log2 = WFM (λf n. if n<=1 then 1 else 1+(f (n DIV 2)) )`

Definition on2bl_def:
  on2bl x = OPTION_MAP n2bl x
End

val univ_rf_def = Define`univ_rf U <=> ∀f. ∃g. ∀x. on2bl (recPhi [f;x]) = U (g++(n2bl x))`

Theorem univ_rf_nonempty:
  univ_rf U ==> {p | U p = SOME x} <> {}
Proof
  rw[univ_rf_def,EXTENSION] >> 
  `∃m. Phi m 0 = SOME (bl2n x)` by (simp[Phi_def] >>
    qexists_tac`dBnum (fromTerm (K @@ church (bl2n x)))` >> simp[] >> qexists_tac`church (bl2n x)` >>
    simp[K_lemma,normal_orderTheory.bnf_bnf_of]) >> 
  `∃g. ∀x. on2bl (Phi m x) = U (g++(n2bl x))` by fs[]>>
  `on2bl (Phi m 0) = U (g++(n2bl 0))` by fs[] >> qexists_tac`g++(n2bl 0)` >> fs[]>>
  `on2bl (SOME (bl2n x)) = U (g ++ n2bl 0)` by metis_tac[] >> 
  fs[optionTheory.OPTION_MAP_DEF,on2bl_def]
QED


Theorem MIN_SET_ladd:
  s <> {} ==>  a + MIN_SET {b | b ∈ s} = MIN_SET { a+b | b ∈ s}
Proof
  rw[] >> `MIN_SET s ∈ s ∧ ∀x. x ∈ s ⇒ MIN_SET s ≤ x` by fs[MIN_SET_LEM] >>
  `(a+MIN_SET s) ∈ {a + b | b ∈ s}` by fs[] >>
  `{a + b | b ∈ s} <> {}` by (`{a + b | b ∈ s} = IMAGE (λx. a+x) s` by metis_tac[IMAGE_DEF]>>
    fs[]) >>
  `MIN_SET {a + b | b ∈ s} ∈ {a + b | b ∈ s} ∧
    ∀x. x ∈ {a + b | b ∈ s} ⇒ MIN_SET {a + b | b ∈ s} ≤ x` by fs[MIN_SET_LEM] >>
  `MIN_SET {a + b | b ∈ s} <= a + MIN_SET s` by fs[] >>
  `∀x. x ∈ s ⇒ a + MIN_SET s ≤ a + x` by fs[] >>
  `{a + b | b ∈ s} = IMAGE (λx. a+x) s` by metis_tac[IMAGE_DEF]>>fs[] >>
  rw[] >> `MIN_SET s <= b` by fs[] >> `b <= MIN_SET s` by fs[] >> fs[]
QED


val recfn_index_def =
new_specification("recfn_index_def", ["recfn_index"],
		  recfns_in_Phi
		      |> SIMP_RULE (srw_ss()) [LEFT_FORALL_IMP_THM]
		      |> SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM])



open reductionEval;

Theorem recfn_SOMEnpair:
  recfn (SOME o (pr2 npair)) 2
Proof
  fs[primrec_recfn,primrec_npair]
QED

Theorem MIN_SET_ADD:
  s<> {} ∧ t <> {} ==> (MIN_SET {b | b∈s} + MIN_SET {a | a∈t} = MIN_SET {a+b | a∈t ∧ b∈s})
Proof
  rw[] >> `MIN_SET s ∈ s ∧ ∀x. x ∈ s ⇒ MIN_SET s ≤ x` by fs[MIN_SET_LEM] >>
  `MIN_SET t ∈ t ∧ ∀x. x ∈ t ⇒ MIN_SET t ≤ x` by fs[MIN_SET_LEM] >>

  `((MIN_SET t) + (MIN_SET s)) ∈ {a + b | a ∈ t ∧ b ∈ s}` by
    (fs[] >> qexists_tac`MIN_SET t` >> qexists_tac`MIN_SET s` >> fs[] ) >>

  `{a + b | a∈t ∧ b ∈ s} <> {}` by (fs[EXTENSION] >> qexists_tac`x'` >> qexists_tac`x` >>fs[]) >>
  `MIN_SET {a + b | a ∈ t ∧ b ∈ s} ∈ {a + b | a ∈ t ∧ b ∈ s} ∧
    ∀x. x ∈ {a + b |a∈t ∧ b ∈ s} ⇒ MIN_SET {a + b | a∈t ∧ b ∈ s} ≤ x` by fs[MIN_SET_LEM] >>
  `MIN_SET {a + b | a ∈ t ∧ b ∈ s} <= MIN_SET t + MIN_SET s` by metis_tac[] >>
  `∀x y. x ∈ s ∧ y∈t ⇒ MIN_SET t + MIN_SET s ≤ y + x` by
    (rw[] >> `MIN_SET s <= x ∧ MIN_SET t <=y` by fs[] >> fs[]) >>
  fs[] >> `MIN_SET s + MIN_SET t <= b'+a'` by fs[] >>
  `a'+b' <= MIN_SET s + MIN_SET t` by fs[] >> fs[]
QED

Theorem MIN_SET_ADD2:
  s<> {} ∧ t <> {} ==> (MIN_SET s + MIN_SET t = MIN_SET {a+b | a∈t ∧ b∈s})
Proof
  `s<> {} ∧ t <> {} ==> (MIN_SET {b | b∈s} + MIN_SET {a | a∈t} = MIN_SET {a+b | a∈t ∧ b∈s})`
    by fs[MIN_SET_ADD] >> fs[]
QED

val kolmog_fn_def = Define`kolmog_fn f = if (∃n. recfn f n)
                                           then SOME (MIN_SET {p | p=recfn_index f})
                                         else NONE`





val _ = export_theory();

