open HolKernel Parse boolLib bossLib

open arithmeticTheory whileTheory logrootTheory pred_setTheory listTheory
open reductionEval;
open churchoptionTheory churchlistTheory recfunsTheory numsAsCompStatesTheory
     kolmogorov_complexityTheory invarianceResultsTheory boolListsTheory
open churchDBTheory
open recursivefnsTheory primrecfnsTheory prtermTheory
open unary_recfnsTheory

val _ = new_theory "kolmog_incomputable"

(*  Proving kolmog is not computable  *)

Definition computable_def:
  computable (f:num->num) <=> ∃i. ∀n. Phi i n = SOME (f n)
End

Theorem ELL_EQ_0[simp]:
  ℓ x = 0 ⇔ x = 0
Proof
  simp[Once num_to_bool_list_def] >> rw[]
QED

Triviality BIT1_smaller: x ≠ 0 ⇒ (x - 1) DIV 2 < x
Proof Cases_on ‘x’ >> simp[ADD1, DIV_LT_X]
QED

Triviality BIT2_smaller:
  x ≠ 0 ∧ EVEN x ⇒ (x - 2) DIV 2 < x
Proof
  Cases_on ‘x’ >> simp[EVEN] >> rename [‘EVEN m’] >> Cases_on ‘m’ >>
  simp[EVEN,ADD1,DIV_LT_X]
QED

Theorem ELL_MONOTONE[simp]:
  ∀x y. x ≤ y ⇒ ℓ x ≤ ℓ y
Proof
  completeInduct_on ‘x’ >> qspec_then ‘x’ mp_tac num_to_bool_list_def >> rw[] >>
  qspec_then ‘y’ mp_tac num_to_bool_list_def >> rw[] >>
  first_x_assum irule >> simp[BIT1_smaller, BIT2_smaller, DIV_LE_MONOTONE] >>
  ‘∃y0. y = 2 * y0’ by metis_tac[EVEN_EXISTS] >> Cases_on ‘y0’ >>
  fs[ADD1, LEFT_ADD_DISTRIB] >>
  ‘∃x0. x = 2 * x0 + 1’ by metis_tac[ODD_EXISTS, ADD1, EVEN_ODD] >>
  Cases_on ‘x0’ >> fs[ADD1, LEFT_ADD_DISTRIB]
QED

Theorem ELL_LE[simp]:
  ℓ k <= k
Proof
  completeInduct_on‘k’ >> qspec_then ‘k’ mp_tac num_to_bool_list_def >> rw[]
  >- (‘(k-2) DIV 2 < k’ by fs[BIT2_smaller] >>
      ‘ℓ ((k-2) DIV 2) ≤ ((k-2) DIV 2)’ by fs[] >>
      ‘ℓ ((k − 2) DIV 2) < k’ by fs[] >> fs[])
  >- (‘(k-1) DIV 2 < k’ by fs[BIT1_smaller] >>
      ‘ℓ ((k-1) DIV 2) ≤ ((k-1) DIV 2)’ by fs[] >>
      ‘ℓ ((k − 1) DIV 2) < k’ by fs[] >> fs[] )
QED

Theorem ELL_LT[simp]:
  ℓ k < k ⇔ 1 < k
Proof
  completeInduct_on ‘k’ >> simp[Once num_to_bool_list_def] >> rw[]
  >- (‘(k - 2) DIV 2 < k’ by simp[BIT2_smaller]>>
      Cases_on ‘1 < (k - 2) DIV 2’
      >- (‘ℓ ((k - 2) DIV 2) < (k - 2) DIV 2’ by metis_tac[] >>
          simp[]) >>
      ‘¬(ℓ ((k - 2) DIV 2) < (k - 2) DIV 2)’ by metis_tac[] >>
      ‘ℓ ((k - 2) DIV 2) = (k - 2) DIV 2’ by metis_tac[LESS_OR_EQ, ELL_LE] >>
      fs[NOT_LESS_EQUAL, X_LT_DIV] >>
      ‘k ≠ 0’ by (strip_tac >> fs[]) >> ‘k ≠ 1’ by (strip_tac >> fs[]) >>
      ‘1 < k’ by simp[] >> simp[] >> fs[DIV_LT_X] >>
      ‘k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5’ by simp[] >> simp[]) >>
  ‘(k - 1) DIV 2 < k’ by simp[BIT1_smaller] >>
  Cases_on ‘1 < (k - 1) DIV 2’
  >- (‘ℓ ((k - 1) DIV 2) < (k - 1) DIV 2’ by metis_tac[] >> simp[]) >>
  ‘¬(ℓ ((k - 1) DIV 2) < (k - 1) DIV 2)’ by metis_tac[] >>
  ‘ℓ ((k - 1) DIV 2) = (k - 1) DIV 2’ by metis_tac[LESS_OR_EQ, ELL_LE] >>
  fs[NOT_LESS_EQUAL, X_LT_DIV, DIV_LT_X] >>
  ‘k = 1 ∨ k = 2 ∨ k = 3 ∨ k= 4’ by simp[] >> simp[]
QED

Theorem contrapos_FINITE_DIFF_down:
  INFINITE P ==> (INFINITE (P DIFF Q) ∨ INFINITE Q)
Proof
  metis_tac[FINITE_DIFF_down]
QED

Theorem INFINITE_DIFF_down:
  INFINITE P ∧ FINITE Q ==> INFINITE (P DIFF Q)
Proof
  rw[] >>  metis_tac[contrapos_FINITE_DIFF_down]
QED

Theorem n2bl_inj[simp]:
  n2bl x = n2bl y <=> x=y
Proof
  eq_tac >> rw[] >> ‘bl2n (n2bl x) = bl2n (n2bl y)’ by metis_tac[] >>
  metis_tac[bool_num_inv]
QED

Theorem computable_imp_thm:
  ∀f. computable f ==> ∃i. ∀n. Phi i n = SOME (f n)
Proof
  metis_tac[computable_def]
QED

Theorem computable_imp_min_thm:
  ∀f. computable f ⇒
      ∃i. (∀n. Phi i n = SOME (f n)) ∧ (∀j. (∀n. Phi j n = SOME (f n)) ==> i<=j)
Proof
  rw[] >>
  qexists_tac‘MIN_SET {i | (∀n. Phi i n = SOME (f n))}’>>
  ‘{i | (∀n. Phi i n = SOME (f n))} <> {}’
    by (fs[EXTENSION,computable_imp_thm]) >>
  rw[]
  >- (‘MIN_SET {i | (∀n. Phi i n = SOME (f n))} ∈
       {i | (∀n. Phi i n = SOME (f n))}’
        by fs[MIN_SET_LEM] >> fs[IN_DEF])
  >- (fs[MIN_SET_LEM])
QED


val recfn_index2_def = new_specification(
  "recfn_index2_def", ["recfn_index2"],
  computable_imp_min_thm
    |> SIMP_RULE (srw_ss()) [LEFT_FORALL_IMP_THM]
    |> SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]);

Theorem ell_0[simp]:
  ℓ 0 = 0
Proof
  EVAL_TAC
QED

Theorem ell_1[simp]:
  ℓ 1 = 1
Proof
  EVAL_TAC
QED

Theorem univ_rf_smallest:
  univ_rf U ∧ U k = SOME y ⇒ KC U y ≤ LENGTH k
Proof
  rw[univ_rf_def] >> simp[KC_def,core_complexity_def] >>
  ‘{p | U p = SOME y} <> ∅’ by (fs[EXTENSION] >> metis_tac[]) >>
  simp[] >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- (simp[EXTENSION] >> metis_tac[]) >>
  fs[PULL_EXISTS]
QED

Theorem univ_rf_kolmog_fn_ub:
  computable f ∧ univ_rf U ==>
  ∃c. ∀m. KC U (n2bl (f m)) ≤ ℓ m + c
Proof
  rw[] >>
  ‘(∀n. Phi (recfn_index2 f) n = SOME (f n)) ∧
   ∀j. (∀n. Phi j n = SOME (f n)) ⇒ recfn_index2 f ≤ j’
    by fs[recfn_index2_def] >>
  ‘∀m. Phi (recfn_index2 f) (m) = SOME (f m)’ by fs[] >>
  ‘∃g. ∀m. on2bl (Phi (recfn_index2 f) m) = (U (g ++ n2bl m))’
    by (fs[univ_rf_def] >>
        ‘∃g. ∀x. on2bl (Phi (recfn_index2 f) x) = (U (g ++ n2bl x))’ by fs[])>>
  qexists_tac‘LENGTH g’ >> rw[] >>
  ‘U (g ++ n2bl m) = SOME (n2bl (f m))’
    by (‘on2bl (Phi (recfn_index2 f) m) = U (g++ n2bl m)’ by fs[] >>
        ‘Phi (recfn_index2 f) m = SOME (f m)’ by fs[] >>
        fs[on2bl_def] >> fs[optionTheory.OPTION_MAP_DEF]) >>
  ‘KC U (n2bl (f m)) ≤ LENGTH (g ++ n2bl m)’ by fs[univ_rf_smallest] >> fs[]
QED

Theorem computable_id:
  computable (λx. x)
Proof
  fs[computable_def,Phi_def] >> qexists_tac‘dBnum (fromTerm (I))’ >>
  rw[] >> qexists_tac‘(church x)’ >> rw[churchnumTheory.force_num_church] >>
  ‘I @@ church x == church x’ by fs[chap2Theory.lameq_I] >>
  ‘bnf (church x)’ by fs[churchnumTheory.bnf_church] >>
  fs[normal_orderTheory.lameq_bnf_of_SOME_I]
QED


Theorem univ_rf_kolmog_ub:
  univ_rf U ==> ∃c. ∀m. KC U (n2bl m) ≤ ℓ m + c
Proof
  rw[] >> ‘computable (λx. x)’ by fs[computable_id] >>
  qabbrev_tac‘f = (λx. (x:num))’ >>
  ‘∃c. ∀m. KC U (n2bl (f m)) <=  ℓ (m)  + c’ by
    metis_tac[univ_rf_kolmog_fn_ub]  >>metis_tac[ADD_COMM]
QED



Definition UKCfkmin_def:
  UKCfkmin (U:bool list->bool list option) m = MIN_SET {bl2n n | m <= KC U n}
End

Theorem univ_rf_kolmog_props:
  univ_rf U ==> ∀y. ∃z. KC U y = LENGTH z ∧ U z = SOME y
Proof
  rw[] >> fs[KC_def,core_complexity_def,univ_rf_nonempty] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >>
  rw[] >> ‘{p | U p = SOME y} ≠ ∅’ by fs[univ_rf_nonempty] >>
  fs[EXTENSION] >> metis_tac[]
QED


Theorem univ_rf_kolmog_lb_exists:
  univ_rf U ==> ∃x. m <= KC U x
Proof
  CCONTR_TAC >> fs[NOT_LESS_EQUAL] >>
  ‘∀x. ∃i. U i = SOME x ∧ LENGTH i < m’ by metis_tac[univ_rf_kolmog_props] >>
  fs[SKOLEM_THM] >>
  ‘FINITE (count m)’ by fs[FINITE_COUNT] >>
  ‘INFINITE {f x | x | T}’ by
    (‘SURJ (λx. U (f x)) UNIV {SOME n|T}’ by
       (fs[SURJ_DEF] >> rw[]) >>
     ‘IMAGE (λx. U (f x) ) UNIV = {SOME n|T}’ by fs[IMAGE_SURJ]>>
     fs[IMAGE_DEF] >>
     ‘{SOME n | T} = IMAGE (λx. U x) {f x | x | T}’ by
       (fs[IMAGE_DEF,EXTENSION] >> rw[] >> eq_tac >> rw[] >> metis_tac[]) >>
     ‘SURJ (λx. U x) {f x | x | T} {SOME n | T}’ by simp[SURJ_IMAGE] >>
     ‘¬(FINITE {SOME (n:bool list) | T})’ by
       (‘INFINITE 𝕌(:bool list option)’ by
          (‘∃f. INJ f 𝕌(:num) 𝕌(:bool list option)’
             suffices_by fs[infinite_num_inj] >>
           qexists_tac‘SOME o n2bl’ >> rw[INJ_DEF,n2bl_inj]) >>
        ‘{SOME n | T} = 𝕌(:bool list option) DIFF {NONE}’ by
          (rw[EXTENSION] >> eq_tac >> rw[] >> Cases_on‘x’ >> fs[]) >>
        ‘FINITE {NONE}’ by fs[FINITE_SING] >>
        rw[] >> fs[INFINITE_DIFF_down]) >>
     ‘∃g. INJ g {SOME n | T} {f x | x | T} ∧
          ∀y. y ∈ {SOME n | T} ⇒ (λx. U x) (g y) = y’ by
       (irule pred_setTheory.SURJ_INJ_INV >> fs[]) >>
     metis_tac[INFINITE_INJ] ) >>
  ‘FINITE {LENGTH i | ∃x. i = (f x)}’ by
    (‘{LENGTH i | ∃x. i = (f x)} ⊆ count (2n**m + 2**m)’ suffices_by
       (metis_tac[SUBSET_FINITE_I,FINITE_COUNT]) >> simp[SUBSET_DEF] >> rw[] >>
     fs[] >>
     ‘LENGTH (f x') < m’ by fs[] >>
     ‘m < 2* 2n** m’ suffices_by fs[] >> ‘m < 2n**m’ by simp[X_LT_EXP_X_IFF] >>
     fs[]) >>
   ‘SURJ (λx. x)  { i | (∃x. i = (f x))} {f x | x | T}’ by
    (fs[SURJ_DEF] >> rw[] ) >>
  ‘FINITE {i | (∃x. i = f x)}’ by
    (‘FINITE {(i:bool list) | LENGTH i < m}’ by
       fs[finite_bool_list_lt_n] >>
     ‘{i | (∃x. i = f x)} ⊆ {i | LENGTH i < m}’
       by (fs[SUBSET_DEF] >> rw[] >> fs[]) >>
     metis_tac[SUBSET_FINITE]) >>
  metis_tac[FINITE_SURJ]
QED

Theorem f_n2bl_min_set_f:
  (∃x. (m:num) ≤ f x) ==> m ≤ f ( n2bl ( MIN_SET {bl2n n | m ≤ f n}))
Proof
  rw[] >> ‘{bl2n n | m ≤ f n} <> {}’ by (fs[EXTENSION] >> metis_tac[]) >>
  ‘n2bl (MIN_SET {bl2n n | m ≤ f n}) ∈ {n | m ≤ f n}’ by
    (‘MIN_SET {bl2n n | m ≤ f n} ∈ {bl2n n | m ≤ f n}’ by fs[MIN_SET_LEM] >>
     ‘n2bl (MIN_SET {bl2n n | m ≤ f n}) ∈ IMAGE n2bl {bl2n n | m ≤ f n}’
       by fs[] >> fs[IMAGE_DEF]) >>
  fs[]
QED

Theorem UKCfkmin_def_lb:
  univ_rf U ==> ∀m. m <= KC U (n2bl (UKCfkmin U m))
Proof
  rw[UKCfkmin_def] >> ‘(∃x. m ≤ KC U x)’ by  fs[univ_rf_kolmog_lb_exists] >>
  ‘m ≤ (λx. KC U x) (n2bl (MIN_SET {bl2n n | m ≤ (λx. KC U x) n}))’
    suffices_by fs[] >>
  irule f_n2bl_min_set_f >> metis_tac[]
QED

Definition unbounded_def: unbounded f = (∀m. ∃x. (m:num) <= f (x:num))
End

val t = brackabs.brackabs_equiv[](ASSUME“LAM "x" (cfindleast
             @@ (LAM "n" (cnot @@ (cless
                              @@ (UM @@ (cnpair @@ (church i) @@ VAR "n") )
                              @@ (VAR "x") ) ) )
             @@ I ) == ZZ”) |> concl |> lhand

Theorem computable_arg_min_set:
  computable f ∧ unbounded f ==> ∃i. ∀x. Phi i x = SOME (MIN_SET {n | x <= f n})
Proof
  rw[computable_def,unbounded_def] >>
  qexists_tac
  ‘dBnum (fromTerm ^t )’ >>
  simp[Phi_def] >> asm_simp_tac (bsrw_ss()) [] >> qx_gen_tac‘x’ >>
  Q.HO_MATCH_ABBREV_TAC‘∃z. bnf_of (cfindleast @@ P @@ I) = _ z ∧ _ z’ >>
  ‘∀n. P @@ church n == cB (x <= f n)’ by
    (asm_simp_tac (bsrw_ss()) [Abbr‘P’] >> rw[] >>
     last_x_assum (qspec_then ‘n’ assume_tac) >>
     drule recfunsTheory.PhiSOME_UM_I >> asm_simp_tac (bsrw_ss()) [] >> fs[]) >>
  ‘(∀n. ∃b. P @@ church n == cB b) ∧ ∃n. P @@ church n == cB T’ by
    (asm_simp_tac (bsrw_ss()) [] >> rw[]) >>
  drule_all_then assume_tac (GEN_ALL churchnumTheory.cfindleast_termI) >>
  asm_simp_tac (bsrw_ss()) [] >> fs[normal_orderTheory.bnf_bnf_of,MIN_SET_DEF]>>
  asm_simp_tac (bsrw_ss()) [] >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

Theorem computable_UKCfkmin:
  univ_rf U ∧ computable (λx. KC U (n2bl x)) ==> computable (UKCfkmin U)
Proof
  rw[] >> ‘unbounded (λx. KC U (n2bl x))’ by
    (rw[unbounded_def] >> ‘∃y. m <= KC U y’ by fs[univ_rf_kolmog_lb_exists] >>
     qexists_tac‘bl2n y’ >> fs[]) >>
  simp[computable_def,UKCfkmin_def] >>
  ‘∃i. ∀n. Phi i n = SOME (MIN_SET { n' | n ≤ (λx. KC U (n2bl x)) n'})’
    suffices_by (rw[] >> qexists_tac‘i’ >> rw[] >>
                 ‘{n' | n ≤ KC U (n2bl n')} = {bl2n n' | n ≤ KC U n'}’
                   suffices_by fs[] >> fs[EXTENSION] >>
                 rw[] >> eq_tac >- (rw[] >> qexists_tac‘n2bl x’ >> fs[])
                 >- (rw[] >> fs[])) >>
  fs[computable_arg_min_set]
QED

Theorem UKCkol_fkmin_lb:
  univ_rf U ∧ computable (λx. KC U (n2bl x)) ==>
  ∃c. ∀m. (λx. KC U (n2bl x)) (UKCfkmin U m) <= (ℓ m)+ c
Proof
  rw[] >> ‘computable (UKCfkmin U)’ by fs[computable_UKCfkmin] >>
  ‘∃c. ∀m. (λx. KC U (n2bl x)) (UKCfkmin U m) ≤ (ℓ m) + c’ by
    metis_tac[univ_rf_kolmog_fn_ub] >> qexists_tac‘c’ >> rw[] >> fs[]
QED

Theorem UKCcompkol_lb:
  univ_rf U ∧ computable (λx. KC U (n2bl x)) ==> ∃c. ∀m. m <=  2*(ℓ m) + c
Proof
  rw[] >>
  ‘∃c. ∀m. (λx. KC U (n2bl x)) (UKCfkmin U m) <= (ℓ m) + c’
    by fs[UKCkol_fkmin_lb]>>
  ‘∀m. m <= (λx. KC U (n2bl x)) (UKCfkmin U m)’ by fs[UKCfkmin_def_lb]  >>
  qexists_tac‘c’ >> rw[] >>
  ‘m ≤ (λx. KC U (n2bl x)) (UKCfkmin U m)’ by fs[] >>
  ‘(λx. KC U (n2bl x)) (UKCfkmin U m) ≤ c + ℓ m’ by fs[] >>fs[]
QED

(* some properties of ℓ; showing how much like log it is *)

(* Make fn which takes n and gives list of nats st log 2 nats = n *)
Definition log2list_def: log2list n = GENLIST (λx. x+2**n) (2**n)
End

Theorem LENGTH_log2list[simp]:
  LENGTH (log2list k) = 2 ** k
Proof
  simp[log2list_def]
QED

Theorem MEM_log2list_ineq:
   MEM x (log2list i) ⇔ 0 < x ∧ (2 ** i)  <= x ∧ x < (2 ** (i+1))
Proof
  eq_tac >> fs[log2list_def,MEM_GENLIST] >> rw[]
  >- (‘x'+2**i < 2** i + 2**i’ by fs[] >>
      ‘(2n**i:num) + 2**i = 2*2**i’ by fs[GSYM TIMES2] >>
      ‘2n**i + 2**i = 2 ** SUC i’ by fs[EXP] >> fs[ADD1])
  >- (qexists_tac‘x-2n**i’ >> fs[] >> ‘2n*2**i = 2 ** SUC i’ by fs[EXP] >>
      fs[ADD1])
QED

Theorem ELL_log2list:
  ∀i n. ℓ n = i ⇔ MEM (n + 1) (log2list i)
Proof
  simp[log2list_def, MEM_GENLIST, PULL_EXISTS] >>
  ‘∀j i. ℓ j = i ⇔ 2 ** i ≤ j + 1 ∧ j + 1 < 2 ** (i + 1)’
     suffices_by (
       rw[] >> reverse eq_tac >> rw[]
       >- simp[LT_SUB_RCANCEL, EXP_ADD] >>
       qexists_tac ‘n - (2 ** i - 1)’ >>
       simp[SUB_LEFT_LESS] >> fs[EXP_ADD]
     ) >>
  completeInduct_on ‘j’ >>
  simp[Once num_to_bool_list_def] >> rw[] >> fs[]
  >- (Cases_on ‘i’ >> fs[EXP] >> fs[DECIDE “x ≤ 1n ⇔ x = 0 ∨ x = 1”]) >>
  simp[DECIDE “SUC x = y ⇔ y ≠ 0 ∧ x = y - 1”] >>
  simp[BIT1_smaller, BIT2_smaller] >> csimp[] >>
  Cases_on ‘i’ >> simp[]
  >- (fs[EVEN_EXISTS] >> rw[] >> fs[] >> rename [‘j0 ≠ 0’] >> Cases_on ‘j0’ >>
      simp[ADD1, LEFT_ADD_DISTRIB] >> rename [‘2 ** n ≤ m + 1 /\ m + 1 < _’] >>
      simp[EXP_ADD]) >>
  fs[GSYM ODD_EVEN, ODD_EXISTS, ADD1, EXP_ADD]
QED

Theorem exp_ELL1:
  2n ** ℓ x <= x+1
Proof
  ‘MEM (x+1) (log2list (ℓ x))’ by metis_tac[ELL_log2list] >>
  fs[MEM_GENLIST,log2list_def]
QED

Theorem exp_ELL2:
  x+1 < 2n ** ((ℓ x)+1 )
Proof
  ‘MEM (x+1) (log2list (ℓ x))’ by metis_tac[ELL_log2list] >>
  fs[MEM_log2list_ineq]
QED

Theorem ell_mult1:
  ℓ(x*y) <= ℓ x + ℓ y +1
Proof
  CCONTR_TAC >> ‘ℓ x + ℓ y +1 < ℓ(x*y)’ by fs[] >>
  ‘2n ** ℓ x <= x+1 ∧ 2 ** ℓ y ≤ y+1 ∧ 2n ** ℓ (x*y) ≤ (x*y)+1’
    by fs[exp_ELL1] >>
  ‘x + 1 < 2n ** (ℓ x + 1) ∧ y + 1 < 2n ** (ℓ y + 1) ∧
   x*y + 1 < 2n ** (ℓ (x*y) + 1)’
    by fs[exp_ELL2] >>
  ‘ℓ x + ℓ y + 2 <= ℓ (x * y)’ by fs[] >>
  ‘2n ** (ℓ x + ℓ y) <= (x+1) * (y+1) ∧
   (x + 1) * (y + 1) < 2n ** (ℓ x + ℓ y + 2)’
    by (fs[LESS_MONO_MULT2,EXP_ADD] >>
        ‘(x + 1 ) * (y + 1) < (2 * 2n ** ℓ x) * (y+1)’ by fs[LT_MULT_LCANCEL] >>
        ‘0<(2 * 2n ** ℓ x)’ by fs[] >>
        ‘(2 * 2n ** ℓ x) * (y+1) < (2 * 2 ** ℓ x ) *  (2 * 2 ** ℓ y)’
          by rw[LT_MULT_LCANCEL] >>
        ‘(x + 1) * (y + 1) < 2 * 2n ** ℓ x * (2 * 2 ** ℓ y)’ by rw[] >> rw[]) >>
  ‘x*y+1 <= (x+1)*(y+1)’ by fs[] >>
  ‘(x + 1) * (y + 1) < 2n ** (ℓ (x*y) )’ by
    (‘2 ** (ℓ x + ℓ y + 2) <= 2n ** (ℓ (x*y))’ by fs[] >> rw[]) >>
  fs[]
QED

Theorem ell_SUC_corr:
   ∀x. ℓ(x+1) ≤ ℓ x + 2
Proof
  rw[] >> Cases_on‘x=0’ >> fs[] >>
  ‘x+1<=2*x’ by (Induct_on‘x’ >> fs[]) >>
  ‘ℓ (x+1) <= ℓ (2*x)’ by fs[ELL_MONOTONE] >>
  ‘ℓ (2*x) <= ℓ x + 2’ suffices_by fs[] >>
  ‘ℓ (2*x) <= ℓ 2 + ℓ x + 1 ’ by fs[ell_mult1] >> fs[] >>
  ‘ℓ 2 + 1 = 2’ by EVAL_TAC >>
  metis_tac[]
QED


Theorem sum_lt_mult:
  x ≠ 0 ∧ y ≠ 0 ∧ x ≠ 1 ∧ y ≠ 1 ==> (x:num) + y ≤ x*y
Proof
  rw[] >> Induct_on‘x’ >> fs[] >> rw[MULT_SUC] >>
  ‘SUC x <= y * x’ suffices_by fs[] >>
  irule MULT_INCREASES >> rw[]
QED

Theorem ell_add_corr:
  ∀n. ∃k. ∀x. ℓ(x+n) <= ℓ(x)+k
Proof
  rw[] >> qexists_tac‘ℓ (n) + 1’ >> rw[] >> Cases_on‘n=0’ >> Cases_on‘x=0’ >>
  fs[] >> Cases_on‘n=1’ >> Cases_on‘x=1’ >> fs[ell_SUC_corr] >- EVAL_TAC >>
  ‘n+x<=n*x’ by fs[sum_lt_mult] >> ‘ℓ (n + x) <= ℓ (n*x)’ by fs[ELL_MONOTONE] >>
  ‘ℓ (n * x) <= ℓ n + (ℓ x + 1)’ suffices_by fs[] >>
  metis_tac[ell_mult1,ADD_ASSOC]
QED

Theorem ell_sum_corr:
  ℓ (x + y) ≤ ℓ x + ℓ y + 1
Proof
  Cases_on‘x=0’ >> Cases_on‘y=0’ >> Cases_on‘x=1’ >> Cases_on‘y=1’ >>
  fs[ell_SUC_corr]
  >- EVAL_TAC >> ‘x+y<= x*y’ by fs[sum_lt_mult] >>
  ‘ℓ (x + y) <= ℓ (x * y)’ by fs[ELL_MONOTONE] >>
  ‘ℓ (x * y) <= ℓ x + (ℓ y + 1)’ suffices_by fs[] >>
  metis_tac[ell_mult1,ADD_ASSOC]
QED

Theorem ell_npair:
  ∃k. ∀x y. ℓ (x ⊗ y) <= 2*(ℓ x + ℓ y) + k
Proof
  ‘∃k. ∀z. ℓ(z+1) <= ℓ(z)+k’ by fs[ell_add_corr] >>
  qexists_tac‘2*k+3’ >> rw[] >>
  fs[numpairTheory.npair_def,numpairTheory.tri_formula] >>
  ‘y + (x + y) * (x + (y + 1)) DIV 2 <= (x+y+1)*(x+y+1)’
    by (‘(x + y) * (x + (y + 1)) DIV 2 <= (x + y) * (x + (y + 1))’
          by fs[DIV_LESS_EQ] >>
        ‘y + (x + y) * (x + (y + 1)) ≤ (x + y + 1) * (x + y + 1)’
          suffices_by fs[] >>
        ‘∃d. y + (x + y) * (x + (y + 1)) + d = (x + y + 1) * (x + y + 1)’
          suffices_by fs[] >>
        qexists_tac‘x+1’ >>
        ONCE_REWRITE_TAC[LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] >>
        ONCE_REWRITE_TAC[LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] >>
        ONCE_REWRITE_TAC[LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] >>
        ONCE_REWRITE_TAC[LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] >> fs[]) >>
  ‘ℓ (y + (x + y) * (x + (y + 1)) DIV 2) <= ℓ ((x + y + 1) * (x + y + 1))’
    by fs[ELL_MONOTONE]>>
  ‘ℓ ((x + y + 1) * (x + y + 1)) <= 2 * k + (2 * (ℓ x + ℓ y) + 3)’
    suffices_by fs[] >>
  ‘ℓ ((x + y + 1) * (x + y + 1)) <= ℓ (x + y + 1) + ℓ (x + y + 1) +1’
    by fs[ell_mult1]>>
  ‘ℓ (x + y + 1) + ℓ (x + y + 1) + 1 <= 2 * k + (2 * (ℓ x + ℓ y) + 3)’
    suffices_by fs[] >>
  ‘ℓ (x+y+1) <= k + ℓ (x+y)’ by fs[] >>
  ‘(ℓ (x + y) + k) + (ℓ (x + y) + k) + 1 <= 2 * k + (2 * (ℓ x + ℓ y) + 3)’
    suffices_by fs[] >>
  fs[] >> ‘2 * ℓ (x + y) ≤ 2 * ( ℓ x + ℓ y ) + 2’ suffices_by fs[] >>
  ‘ℓ (x + y) ≤ (ℓ x + ℓ y) + 1’ suffices_by fs[] >> metis_tac[ell_sum_corr]
QED

Theorem exists_log_lb:
  ∃m. ¬(m<= 2*(ℓ m) + c)
Proof
  CCONTR_TAC >> fs[] >>
  Cases_on‘1<c’
  >- (‘ℓ c < c’ by fs[ELL_LT] >> ‘11*c <= c + 2 * ℓ (11*c)’ by fs[] >>
      ‘ℓ (11*c) <= ℓ 11 + ℓ c + 1’ by fs[ell_mult1] >>
      ‘11*c<= c+ 2* (ℓ 11 + ℓ c + 1)’ by fs[] >>
      ‘5*c <= (ℓ 11 + ℓ c + 1)’ by fs[] >>
      ‘ℓ 11 = 3’ by EVAL_TAC >> fs[] >> ‘ℓ c + 4 < c + 4’ by fs[ELL_LT] >>
      ‘5*c < c+4’ by metis_tac[LESS_EQ_LESS_TRANS] >>
      ‘c+4 < 4*c + c’ by fs[] >> fs[])
  >- (‘c<=1’ by fs[] >> ‘c=0 ∨ c=1’ by fs[] >> fs[]
      >- (‘100 <= 2 * ℓ 100’ by fs[] >> pop_assum mp_tac >> EVAL_TAC)
      >- (‘100 <= 2 * ℓ 100 + 1’ by fs[] >> pop_assum mp_tac >> EVAL_TAC)  )
QED

Theorem part_hutter_UKC:
  univ_rf U ∧ computable (λx. KC U (n2bl x)) ==> F
Proof
  strip_tac >> ‘∃c. ∀m. m <=  2*(ℓ m) + c’ by metis_tac[UKCcompkol_lb] >>
  ‘∃m. ¬(m<= 2*(ℓ m) + c)’ by fs[exists_log_lb] >> metis_tac[]
QED

Theorem UKC_incomp:
  univ_rf U ==> ¬(computable (λx. KC U (n2bl x)))
Proof
  metis_tac[part_hutter_UKC]
QED

val _ = export_theory()
