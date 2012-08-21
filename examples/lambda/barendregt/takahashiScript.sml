open HolKernel Parse boolLib bossLib lcsymtacs
open binderLib

open termTheory chap3Theory

val _ = new_theory "takahashi"

val redAPP_exists =
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

val redAPP_LAM = prove(
  ``redAPP (LAM v M) N = [N/v]M``,
  Q_TAC (NEW_TAC "z") `{v} ∪ FV M ∪ FV N` >>
  `LAM v M = LAM z ([VAR z/v]M)` by rw[SIMPLE_ALPHA] >>
  simp[redAPP_def, lemma15a]);

(*

redAPP applies term 1 to term 2, unless term 2 is an abstraction, in
which case it performs a β-reduction:

   redAPP (VAR s) P = VAR s @@ p
   redAPP (M @@ N) P = M @@ N @@ P
   redAPP (LAM v M) N = [N/v]M
*)

val redAPP_thm = save_thm(
  "redAPP_thm",
  redAPP_def
      |> CONJ_PAIR
      |> apfst
           (fn th1 => th1 |> CONJUNCTS |> front_last |> #1
                          |> (fn l => l @ [GEN_ALL redAPP_LAM]) |> LIST_CONJ)
      |> uncurry CONJ)
val _ = export_rewrites ["redAPP_thm"]

val pmact_COND = prove(
  ``pmact a pi (COND p q r) = COND p (pmact a pi q) (pmact a pi r)``,
  rw[]);

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
val tstar_redex =
    tstar_thm |> CONJUNCTS |> el 2
              |> Q.INST [`M` |-> `LAM v M`]
              |> SIMP_RULE (srw_ss()) [last (CONJUNCTS tstar_thm)]

val _ = overload_on("RTC", ``tstar``)

val varreflind_refl = prove(
  ``∀P X. (∀s. P (VAR s) (VAR s)) ∧
          (∀v M1 M2. v ∉ X ∧ P M1 M2 ⇒ P (LAM v M1) (LAM v M2)) ∧
          (∀M1 M2 N1 N2. P M1 M2 ∧ P N1 N2 ⇒
                         P (M1 @@ N1) (M2 @@ N2)) ∧
          (∀M1 M2 N1 N2 v.
             v ∉ X ∧ v ∉ FV N1 ∧ v ∉ FV N2 ∧ P M1 M2 ∧ P N1 N2 ⇒
             P (LAM v M1 @@ N1) ([N2/v]M2)) ∧ FINITE X ⇒
    ∀M. P M M``,
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac nc_INDUCTION2 >> qexists_tac `X` >> simp[])

val varreflind0 = prove(
  ``∀P X. (∀s. P (VAR s) (VAR s)) ∧
          (∀v M1 M2. v ∉ X ∧ P M1 M2 ⇒ P (LAM v M1) (LAM v M2)) ∧
          (∀M1 M2 N1 N2. P M1 M2 ∧ P N1 N2 ⇒
                         P (M1 @@ N1) (M2 @@ N2)) ∧
          (∀M1 M2 N1 N2 v.
             v ∉ X ∧ v ∉ FV N1 ∧ v ∉ FV N2 ∧ P M1 M2 ∧ P N1 N2 ⇒
             P (LAM v M1 @@ N1) ([N2/v]M2)) ∧ FINITE X ⇒
    ∀M N. M =β=> N ⇒ P M N``,
  rpt gen_tac >> strip_tac >> ho_match_mp_tac grandbeta_bvc_ind >>
  qexists_tac `X` >> simp[] >>
  match_mp_tac varreflind_refl >> qexists_tac `X` >> simp[])

val varreflind =
    varreflind0
        |> Q.SPEC `λM N. P M N ∧ M =β=> N`
        |> SIMP_RULE (srw_ss()) [grandbeta_rules, GSYM CONJ_ASSOC]

val grandbeta_refl = store_thm(
  "grandbeta_refl",
  ``M =β=> M``,
  simp[grandbeta_rules]);
val _ = export_rewrites ["grandbeta_refl"]

val takahashi_5 = store_thm(
  "takahashi_5",
  ``∀M N. M =β=> N ⇒ N =β=> M^*``,
  ho_match_mp_tac varreflind >> qexists_tac `{}` >>
  simp[tstar_thm, grandbeta_rules] >>
  rpt conj_tac
  >- (map_every qx_gen_tac [`M1`, `M2`, `N1`, `N2`] >> strip_tac >>
      Tactical.REVERSE (Cases_on `is_abs M1`) >- simp[grandbeta_rules] >>
      `∃v M0. M1 = LAM v M0`
         by (qspec_then `M1` FULL_STRUCT_CASES_TAC term_CASES >> fs[] >>
             metis_tac[]) >>
      fs[tstar_thm, abs_grandbeta] >> fs[abs_grandbeta, grandbeta_rules]) >>
  simp[grandbeta_subst])

val grandbeta_diamond = store_thm(
  "grandbeta_diamond",
  ``diamond_property $=b=>``,
  metis_tac [takahashi_5, diamond_property_def]);

val _ = export_theory()
