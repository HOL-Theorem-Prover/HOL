Theory takahashi
Ancestors
  term chap3
Libs
  binderLib

(* based on

   Masako Takahashi. Parallel reductions in λ-calculus.
   Information and Computation, 1995.
   doi:10.1006/inco.1995.1057.

*)

Theorem redAPP_exists[local] =
    parameter_tm_recursion
        |> INST_TYPE [alpha |-> ``:term``, ``:ρ`` |-> ``:term``]
        |> Q.INST [`ap` |-> `\rt ru t u p. t @@ u @@ p`,
                   `lm` |-> `\rt v t p. [p/v]t`,
                   `vr` |-> `\s p. VAR s @@ p`,
                   `apm` |-> `term_pmact`, `ppm` |-> `term_pmact`,
                   `A` |-> `{}`]
        |> SIMP_RULE (srw_ss()) [tpm_subst]
        |> SIMP_RULE (srw_ss()) [fresh_tpm_subst, lemma15a]

val redAPP_def = new_specification("redAPP_def", ["redAPP"], redAPP_exists)

Theorem redAPP_LAM[local]:
  redAPP (LAM v M) N = [N/v]M
Proof
  Q_TAC (NEW_TAC "z") `{v} ∪ FV M ∪ FV N` >>
  `LAM v M = LAM z ([VAR z/v]M)` by rw[SIMPLE_ALPHA] >>
  simp[redAPP_def, lemma15a]
QED

(*

redAPP applies term 1 to term 2, unless term 2 is an abstraction, in
which case it performs a β-reduction:

   redAPP (VAR s) P = VAR s @@ p
   redAPP (M @@ N) P = M @@ N @@ P
   redAPP (LAM v M) N = [N/v]M
*)

Theorem redAPP_thm[simp] =
  redAPP_def
      |> CONJ_PAIR
      |> apfst
           (fn th1 => th1 |> CONJUNCTS |> front_last |> #1
                          |> (fn l => l @ [GEN_ALL redAPP_LAM]) |> LIST_CONJ)
      |> uncurry CONJ

Theorem pmact_COND[local]:
  pmact a pi (COND p q r) = COND p (pmact a pi q) (pmact a pi r)
Proof
  rw[]
QED

(* Takahashi's superscript star operator *)
val (tstar_thm, tpm_tstar) = define_recursive_term_function'
  (SIMP_CONV (srw_ss()) [tpm_ALPHA,pmact_COND])
`
  (tstar (VAR s) = VAR s) ∧
  (tstar (APP M N) = if is_abs M then redAPP (tstar M) (tstar N)
                     else tstar M @@ tstar N) ∧
  (tstar (LAM v M) = LAM v (tstar M))
`;

(* tstar (LAM v M @@ N) = [tstar N/v] (tstar M) *)
Theorem tstar_redex =
    tstar_thm |> CONJUNCTS |> el 2
              |> Q.INST [`M` |-> `LAM v M`]
              |> SIMP_RULE (srw_ss()) [last (CONJUNCTS tstar_thm)]

val _ = overload_on("RTC", ``tstar``)

Theorem varreflind_refl[local]:
  ∀P X. (∀s. P (VAR s) (VAR s)) ∧
        (∀v M1 M2. v ∉ X ∧ P M1 M2 ⇒ P (LAM v M1) (LAM v M2)) ∧
        (∀M1 M2 N1 N2. P M1 M2 ∧ P N1 N2 ⇒
                       P (M1 @@ N1) (M2 @@ N2)) ∧
        (∀M1 M2 N1 N2 v.
           v ∉ X ∧ v ∉ FV N1 ∧ v ∉ FV N2 ∧ P M1 M2 ∧ P N1 N2 ⇒
           P (LAM v M1 @@ N1) ([N2/v]M2)) ∧ FINITE X ⇒
        ∀M. P M M
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac nc_INDUCTION2 >> qexists_tac `X` >> simp[]
QED

Theorem varreflind0[local]:
  ∀P X. (∀s. P (VAR s) (VAR s)) ∧
        (∀v M1 M2. v ∉ X ∧ P M1 M2 ⇒ P (LAM v M1) (LAM v M2)) ∧
        (∀M1 M2 N1 N2. P M1 M2 ∧ P N1 N2 ⇒
                       P (M1 @@ N1) (M2 @@ N2)) ∧
        (∀M1 M2 N1 N2 v.
           v ∉ X ∧ v ∉ FV N1 ∧ v ∉ FV N2 ∧ P M1 M2 ∧ P N1 N2 ⇒
           P (LAM v M1 @@ N1) ([N2/v]M2)) ∧ FINITE X ⇒
    ∀M N. M =β=> N ⇒ P M N
Proof
  rpt gen_tac >> strip_tac >> ho_match_mp_tac grandbeta_bvc_ind >>
  qexists_tac `X` >> simp[] >>
  match_mp_tac varreflind_refl >> qexists_tac `X` >> simp[]
QED

Theorem varreflind[local] =
    varreflind0
        |> Q.SPEC `λM N. P M N ∧ M =β=> N`
        |> SIMP_RULE (srw_ss()) [grandbeta_rules, GSYM CONJ_ASSOC]

Theorem grandbeta_refl[simp]:
  M =β=> M
Proof
  simp[grandbeta_rules]
QED

Theorem takahashi_5:
  ∀M N. M =β=> N ⇒ N =β=> M^*
Proof
  ho_match_mp_tac varreflind >> qexists_tac `{}` >>
  simp[tstar_thm, grandbeta_rules] >>
  rpt conj_tac
  >- (map_every qx_gen_tac [`M1`, `M2`, `N1`, `N2`] >> strip_tac >>
      Tactical.REVERSE (Cases_on `is_abs M1`) >- simp[grandbeta_rules] >>
      `∃v M0. M1 = LAM v M0`
         by (qspec_then `M1` FULL_STRUCT_CASES_TAC term_CASES >> fs[] >>
             metis_tac[]) >>
      fs[tstar_thm, abs_grandbeta] >> fs[abs_grandbeta, grandbeta_rules]) >>
  simp[grandbeta_subst]
QED

Theorem grandbeta_diamond:
  diamond_property $=b=>
Proof
  metis_tac [takahashi_5, diamond_property_def]
QED
