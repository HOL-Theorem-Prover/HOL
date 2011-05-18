(* this is an -*- sml -*- file *)
open HolKernel Parse boolLib

open BasicProvers
open bossLib binderLib
open pretermTheory basic_swapTheory nomsetTheory
open pred_setTheory

fun Store_Thm(s, t, tac) = (store_thm(s,t,tac) before export_rewrites [s])
fun Save_Thm(s, th) = (save_thm(s, th) before export_rewrites [s])

val _ = new_theory "term"
(* perform quotient *)

fun mk_def(s,t) =
    {def_name = s ^ "_def", fixity = Prefix, fname = s, func = t};
val app_respects_aeq = List.nth(CONJUNCTS aeq_rules, 1)

val ptpm_fv' = (CONV_RULE (BINDER_CONV
                             (RAND_CONV (SIMP_CONV (srw_ss()) [perm_IN]))) o
                REWRITE_RULE [EXTENSION]) ptpm_fv

val [FV_thm, FV_tpm, simple_induction, tpm_thm, term_distinct, term_11,
     LAM_eq_thm, FRESH_swap0,
     FINITE_FV,
     tpm_sing_inv, tpm_NIL, tpm_inverse, tpm_flip_args, tpm_id_front] =
    quotient.define_equivalence_type
    {
     name = "term", equiv = aeq_equiv,
     defs = map mk_def [("LAM", ``lam``), ("@@", ``app``),
                        ("VAR", ``var``), ("FV", ``fv``),
                        ("tpm", ``ptpm``)],
     welldefs = [lam_respects_aeq, app_respects_aeq, var_respects_aeq, aeq_fv,
                 SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] aeq_ptpm_lemma
                 ],
     old_thms = [fv_def, ptpm_fv',
                 TypeBase.induction_of ``:preterm$preterm``, ptpm_def,
                 aeq_distinct, aeq_ptm_11,
                 lam_aeq_thm, fresh_swap, (* ptpm_is_perm,*)
                 finite_fv,
                 ptpm_sing_inv, ptpm_NIL, ptpm_INVERSE, ptpm_flip_args,
                 ptpm_id_front]}
val _ = set_fixity "@@" (Infixl 901);
val _ = set_MLname "@@_def" "APP_def"

(* hide all of preterm's constants *)
val _ = List.app (fn s => remove_ovl_mapping s {Name = s, Thy = "preterm"})
                 ["fv", "var", "app", "lam", "ptpm", "aeq"]

val _ = Save_Thm("FINITE_FV", FINITE_FV);
val _ = Save_Thm("FV_thm", FV_thm);
val _ = Save_Thm("FV_tpm", FV_tpm)
val _ = Save_Thm("term_11", term_11);
val _ = Save_Thm("term_distinct", term_distinct);
val _ = Save_Thm("tpm_NIL", tpm_NIL)
val _ = Save_Thm("tpm_id_front", tpm_id_front)
val _ = Save_Thm("tpm_inverse", tpm_inverse);
val _ = Save_Thm("tpm_sing_inv", tpm_sing_inv);
val _ = Save_Thm("tpm_thm", tpm_thm);

val tpm_fresh = save_thm("tpm_fresh", GSYM FRESH_swap0)

val FRESH_APP = Store_Thm(
  "FRESH_APP",
  ``v NOTIN FV (M @@ N) <=> v NOTIN FV M /\ v NOTIN FV N``,
  SRW_TAC [][]);
val FRESH_LAM = Store_Thm(
  "FRESH_LAM",
  ``u NOTIN FV (LAM v M) <=> (u <> v ==> u NOTIN FV M)``,
  SRW_TAC [][] THEN METIS_TAC []);
val FV_EMPTY = store_thm(
  "FV_EMPTY",
  ``(FV t = {}) <=> !v. v NOTIN FV t``,
  SIMP_TAC (srw_ss()) [EXTENSION]);

(* quote the term in order to get the variable names specified *)
val simple_induction = store_thm(
  "simple_induction",
  ``!P. (!s. P (VAR s)) /\
        (!M N. P M /\ P N ==> P (M @@ N)) /\
        (!v M. P M ==> P (LAM v M)) ==>
        !M. P M``,
  METIS_TAC [simple_induction])

val _ = save_thm("LAM_eq_thm", LAM_eq_thm);
val _ = save_thm("tpm_flip_args", tpm_flip_args)

(* this result doesn't seem liftable through the quotienting mechanism *)
val tpm_is_perm = Store_Thm(
  "tpm_is_perm",
  ``is_perm tpm``,
  SRW_TAC [][is_perm_def, FUN_EQ_THM, permeq_def] THEN
  Q.ID_SPEC_TAC `x` THEN HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][lswapstr_APPEND]);

(* immediate consequence *)
val tpm_APPEND = store_thm(
  "tpm_APPEND",
  ``tpm (p1 ++ p2) t = tpm p1 (tpm p2 t)``,
  METIS_TAC [is_perm_def, tpm_is_perm]);

(* more minor results about tpm *)
val tpm_eql = store_thm(
  "tpm_eql",
  ``(tpm pi t = u) = (t = tpm (REVERSE pi) u)``,
  METIS_TAC [tpm_inverse]);
val tpm_eqr = store_thm(
  "tpm_eqr",
  ``(t = tpm pi u) = (tpm (REVERSE pi) t = u)``,
  METIS_TAC [tpm_inverse]);

val tpm_sing_to_back = store_thm(
  "tpm_sing_to_back",
  ``!t. tpm [(lswapstr p u, lswapstr p v)] (tpm p t) = tpm p (tpm [(u,v)] t)``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][basic_swapTheory.lswapstr_sing_to_back]);

val tpm_CONS = store_thm(
  "tpm_CONS",
  ``tpm ((x,y)::pi) t = tpm [(x,y)] (tpm pi t)``,
  SRW_TAC [][GSYM tpm_APPEND]);

val tpm_ALPHA = store_thm(
  "tpm_ALPHA",
  ``v ∉ FV u ==> (LAM x u = LAM v (tpm [(v,x)] u))``,
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, tpm_flip_args]);

(* ----------------------------------------------------------------------
    BVC-compatible structural induction (fixed context)
   ---------------------------------------------------------------------- *)

val nc_INDUCTION2 = store_thm(
  "nc_INDUCTION2",
  ``!P X.
      (!x. P (VAR x)) /\ (!t u. P t /\ P u ==> P (t @@ u)) /\
      (!y u. ~(y IN X) /\ P u ==> P (LAM y u)) /\ FINITE X ==>
      !u. P u``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!u pi. P (tpm pi u)` THEN1 METIS_TAC [tpm_NIL] THEN
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][] THEN
  Q_TAC (NEW_TAC "z") `lswapstr pi v INSERT FV (tpm pi u) UNION X` THEN
  Q_TAC SUFF_TAC `LAM (lswapstr pi v) (tpm pi u) =
                  LAM z (tpm ((z,lswapstr pi v)::pi) u)`
        THEN1 SRW_TAC [][] THEN
  SRW_TAC [][LAM_eq_thm, lswapstr_APPEND] THENL [
    FULL_SIMP_TAC (srw_ss()) [],
    SRW_TAC [][tpm_eqr, tpm_flip_args, tpm_APPEND]
  ]);

(* cases theorem *)
val term_CASES = store_thm(
  "term_CASES",
  ``!t. (?s. t = VAR s) \/ (?t1 t2. t = t1 @@ t2) \/ (?v t0. t = LAM v t0)``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][] THEN METIS_TAC []);

(* "acyclicity" *)
val APP_acyclic = store_thm(
  "APP_acyclic",
  ``!t1 t2. t1 <> t1 @@ t2 /\ t1 <> t2 @@ t1``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);

val (tmrecrel_rules, tmrecrel_ind, tmrecrel_cases) = Hol_reln`
  (∀s. tmrecrel A vf af lf (VAR s) (vf s)) /\
  (∀t1 t2 r1 r2. tmrecrel A vf af lf t1 r1 /\ tmrecrel A vf af lf t2 r2 ==>
   tmrecrel A vf af lf (t1 @@ t2) (af r1 r2 t1 t2)) /\
  (∀v r t. v ∉ A ∧ tmrecrel A vf af lf t r ==>
   tmrecrel A vf af lf (LAM v t) (lf v r t))
`;

open lcsymtacs
val tmrecrel_total = prove(
  ``FINITE A ==> ∀t. ∃r. tmrecrel A vf af lf t r``,
  strip_tac >> ho_match_mp_tac nc_INDUCTION2 >> qexists_tac `A` >>
  metis_tac [tmrecrel_rules]);

val eqv_helpers =
``(∀x y s. x ∉ A ∧ y ∉ A ==> (apm [(x,y)] (vf s : 'a) = vf (swapstr x y s))) ∧
  (∀x y t1 t2 r1 r2.
     x ∉ A ∧ y ∉ A ∧
     (∀x. x ∉ A ∧ x ∉ FV t1 ==> x ∉ supp apm r1) ∧
     (∀x. x ∉ A ∧ x ∉ FV t2 ==> x ∉ supp apm r2) ==>
      (apm [(x,y)] (af r1 r2 t1 t2) =
       af (apm [(x,y)] r1) (apm [(x,y)] r2) (tpm [(x,y)] t1) (tpm [(x,y)] t2)))
     ∧
  (∀x y v t r.
     x ∉ A ∧ y ∉ A ∧ v ∉ A ∧
     (∀x. x ∉ A ∧ x ∉ FV t ==> x ∉ supp apm r) ==>
     (apm [(x,y)] (lf v r t) =
      lf (swapstr x y v) (apm [(x,y)] r) (tpm [(x,y)] t)))``

val FCB =
  ``∀a r:α t:term. a ∉ A ∧ (∀x. x ∉ A ∧ x ∉ FV t ==> x ∉ supp apm r) ==>
                   a ∉ supp apm (lf a r t:α)``

val notinsupp_I = prove(
  ``∀A apm e x.
       is_perm apm ∧ FINITE A ∧ support apm x A ∧ e ∉ A ==> e ∉ supp apm x``,
  metis_tac [supp_smallest, SUBSET_DEF]);

val tmrecrel_eqvfresh = prove(
  ``FINITE A ∧ is_perm apm ∧ ^eqv_helpers ∧ ^FCB ==>
    ∀t r. tmrecrel A vf af lf t r ==>
          (∀x y. x ∉ A ∧ y ∉ A ==>
                 tmrecrel A vf af lf (tpm [(x,y)] t) (apm [(x,y)] r)) ∧
          (∀x. x ∉ A ∧ x ∉ FV t ==> x ∉ supp apm r)``,
  strip_tac >> Induct_on `tmrecrel A vf af lf` >> srw_tac [][] >| [
    srw_tac [][tmrecrel_rules],
    match_mp_tac notinsupp_I >> qexists_tac `s INSERT A` >>
    srw_tac [][support_def],
    metis_tac [tmrecrel_rules],
    match_mp_tac notinsupp_I >> qexists_tac `FV t ∪ FV t' ∪ A` >>
    srw_tac [][support_def, supp_fresh, tpm_fresh],
    `swapstr x y v ∉ A` by srw_tac [][swapstr_def] >>
    metis_tac [tmrecrel_rules],
    Cases_on `x = v` >> srw_tac [][] >>
    match_mp_tac notinsupp_I >> qexists_tac `A ∪ FV t ∪ {v}` >>
    srw_tac [][support_def, supp_fresh, tpm_fresh]
  ]);

fun udplus th =
    th |> REWRITE_RULE [GSYM CONJ_ASSOC]
       |> repeat (UNDISCH o CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)))
       |> UNDISCH

val eqvfresh_I = udplus tmrecrel_eqvfresh

val uniqueness = prove(
  ``FINITE A ∧ is_perm apm ∧ ^eqv_helpers ∧ ^FCB ==>
    ∀t r. tmrecrel A vf af lf t r ==>
          ∀r'. tmrecrel A vf af lf t r' ==> (r = r')``,
  strip_tac >> Induct_on `tmrecrel` >> rpt conj_tac
    >- (srw_tac [][Once tmrecrel_cases])
    >- (rpt gen_tac >> strip_tac >> srw_tac [][Once tmrecrel_cases] >>
        metis_tac []) >>
  map_every qx_gen_tac [`v`, `r`, `t`] >>
  strip_tac >> simp_tac (srw_ss()) [Once tmrecrel_cases] >>
  qx_gen_tac `r'` >> simp_tac (srw_ss() ++ boolSimps.DNF_ss)[] >>
  map_every qx_gen_tac [`u`, `r2`, `t2`] >> srw_tac [][] >>
  Cases_on `v = u` >- (fsrw_tac [][] >> metis_tac []) >>
  `t2 = tpm [(u,v)] t` by fsrw_tac [][LAM_eq_thm, tpm_flip_args] >>
  `tmrecrel A vf af lf t (apm [(u,v)] r2)`
     by metis_tac [tpm_sing_inv, eqvfresh_I] >>
  `r = apm [(u,v)] r2` by metis_tac [] >>
  fsrw_tac [][tpm_eqr] >> srw_tac [][] >>
  `∀a. a ∉ A ∧ a ∉ FV t2 ==> a ∉ supp apm r2` by metis_tac [eqvfresh_I] >>
  `v ∉ FV t2`
    by (first_x_assum (MP_TAC o AP_TERM ``λt. (v:string) ∈ FV t``) >>
        srw_tac [][]) >>
  `v ∉ supp apm r2` by metis_tac [eqvfresh_I] >>
  `v ∉ supp apm (lf u r2 t2)`
     by (match_mp_tac notinsupp_I >>
         qexists_tac `A ∪ {u} ∪ supp apm r2 ∪ FV t2` >>
         srw_tac [][tpm_fresh, supp_fresh, support_def] >>
         match_mp_tac (GEN_ALL supp_absence_FINITE) >> metis_tac[]) >>
  `u ∉ supp apm (lf u r2 t2)` by metis_tac [] >>
  Q.MATCH_ABBREV_TAC `X = Y` >> qsuff_tac `apm [(u,v)] X = apm [(u,v)] Y`
    >- srw_tac [][is_perm_injective] >>
  markerLib.UNABBREV_ALL_TAC >>
  `∀x. x ∉ A ∧ x ∉ FV (tpm [(u,v)] t2) ==> x ∉ supp apm (apm [(u,v)] r2)`
     by metis_tac [eqvfresh_I] >>
  srw_tac [][SimpLHS, is_perm_sing_inv] >> metis_tac [supp_fresh]);

val tm_recursion0 = prove(
  ``FINITE A ∧ is_perm apm ∧ ^eqv_helpers ∧ ^FCB ==>
    ∃f. ((∀s. f (VAR s) = vf s) ∧
         (∀t1 t2. f (t1 @@ t2) = af (f t1) (f t2) t1 t2) ∧
         (∀v t. v ∉ A ==> (f (LAM v t) = lf v (f t) t))) ∧
        ∀x y t. x ∉ A ∧ y ∉ A ==>
                 (f (tpm [(x,y)] t) = apm [(x,y)] (f t))``,
  strip_tac >> qexists_tac `λt. @r. tmrecrel A vf af lf t r` >>
  srw_tac [][] >| [
    srw_tac [][Once tmrecrel_cases],
    assume_tac (udplus uniqueness) >>
    REWRITE_TAC [Once tmrecrel_cases] >> simp_tac (srw_ss()) [] >>
    `∃r1 r2. tmrecrel A vf af lf t1 r1 ∧ tmrecrel A vf af lf t2 r2`
      by metis_tac [udplus tmrecrel_total] >>
    `(∀r. tmrecrel A vf af lf t1 r = (r = r1)) ∧
     ∀r. tmrecrel A vf af lf t2 r = (r = r2)` by metis_tac [] >>
    srw_tac [][],

    `∃r. tmrecrel A vf af lf t r` by metis_tac [udplus tmrecrel_total] >>
    `tmrecrel A vf af lf (LAM v t) (lf v r t)` by metis_tac [tmrecrel_rules] >>
    `(∀r'. tmrecrel A vf af lf t r' = (r' = r)) ∧
     ∀r'. tmrecrel A vf af lf (LAM v t) r' = (r' = lf v r t)`
      by metis_tac [udplus uniqueness] >>
    srw_tac [][],

    `∃r. tmrecrel A vf af lf t r` by metis_tac [udplus tmrecrel_total] >>
    `tmrecrel A vf af lf (tpm [(x,y)] t) (apm [(x,y)] r)`
      by metis_tac [eqvfresh_I] >>
    `(∀r'. tmrecrel A vf af lf t r' = (r' = r)) ∧
     ∀r'. tmrecrel A vf af lf (tpm [(x,y)] t) r' = (r' = apm [(x,y)] r)`
      by metis_tac [udplus uniqueness] >>
    srw_tac [][]
  ]);

val tm_recursion = save_thm(
  "tm_recursion",
  tm_recursion0
      |> Q.INST [`vf` |-> `vr`, `af` |-> `ap`, `lf` |-> `λv r t. lm r v t`]
      |> BETA_RULE)

(* ----------------------------------------------------------------------
    Establish substitution function
   ---------------------------------------------------------------------- *)

val tpm_COND = prove(
  ``tpm pi (if P then x else y) = if P then tpm pi x else tpm pi y``,
  SRW_TAC [][]);

val tpm_apart = store_thm(
  "tpm_apart",
  ``!t. ~(x IN FV t) /\ (y IN FV t) ==> ~(tpm [(x,y)] t = t)``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][] THENL [
    METIS_TAC [],
    METIS_TAC [],
    SRW_TAC [][LAM_eq_thm] THEN
    Cases_on `x = v` THEN SRW_TAC [][]
  ]);

val supp_tpm = Store_Thm(
  "supp_tpm",
  ``supp tpm = FV``,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC supp_unique_apart THEN SRW_TAC [][support_def, tpm_fresh] THEN
  METIS_TAC [tpm_apart, tpm_flip_args]);

val subst_exists =
    tm_recursion
        |> INST_TYPE [alpha |-> ``:term``]
        |> SPEC_ALL
        |> Q.INST [`A` |-> `x INSERT FV N`, `apm` |-> `tpm`,
                   `vr` |-> `\s. if s = x then N else VAR s`,
                   `ap` |-> `\r1 r2 t1 t2. r1 @@ r2`,
                   `lm` |-> `\r v t. LAM v r`]
        |> SIMP_RULE (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def,
                                 tpm_COND, tpm_fresh]
        |> SIMP_RULE (srw_ss()) [swapstr_eq_left]
        |> Q.GEN `x` |> Q.GEN `N`
        |> SIMP_RULE (srw_ss()) [SKOLEM_THM, FORALL_AND_THM]

val SUB_DEF = new_specification("SUB_DEF", ["SUB"], subst_exists)

val _ = add_rule {term_name = "SUB", fixity = Closefix,
                  pp_elements = [TOK "[", TM, TOK "/", TM, TOK "]"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2))};

(* Give substitution theorems names compatible with historical usage *)

val SUB_THMv = prove(
  ``([N/x](VAR x) = N) /\ (~(x = y) ==> ([N/y](VAR x) = VAR x))``,
  SRW_TAC [][SUB_DEF]);
val SUB_THM = save_thm(
  "SUB_THM",
  REWRITE_RULE [GSYM CONJ_ASSOC]
               (LIST_CONJ (SUB_THMv :: tl (CONJUNCTS SUB_DEF))))
val _ = export_rewrites ["SUB_THM"]
val SUB_VAR = save_thm("SUB_VAR", hd (CONJUNCTS SUB_DEF))

(* ----------------------------------------------------------------------
    Results about substitution
   ---------------------------------------------------------------------- *)

val fresh_tpm_subst = store_thm(
  "fresh_tpm_subst",
  ``!t. ~(u IN FV t) ==> (tpm [(u,v)] t = [VAR u/v] t)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val tpm_subst = store_thm(
  "tpm_subst",
  ``!N. tpm pi ([M/v] N) = [tpm pi M/lswapstr pi v] (tpm pi N)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `v INSERT FV M` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val tpm_subst_out = store_thm(
  "tpm_subst_out",
  ``[M/v] (tpm pi N) =
       tpm pi ([tpm (REVERSE pi) M/lswapstr (REVERSE pi) v] N)``,
  SRW_TAC [][tpm_subst])

val lemma14a = Store_Thm(
  "lemma14a",
  ``!t. [VAR v/v] t = t``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR])
val lemma14b = store_thm(
  "lemma14b",
  ``!M. ~(v IN FV M) ==> ([N/v] M = M)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `v INSERT FV N` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);
val lemma14c = store_thm(
  "lemma14c",
  ``!t x u. x IN FV u ==> (FV ([t/x]u) = FV t UNION (FV u DELETE x))``,
  NTAC 2 GEN_TAC THEN HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `x INSERT FV t` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, EXTENSION] THENL [
    Cases_on `x IN FV u'` THEN SRW_TAC [][lemma14b] THEN METIS_TAC [],
    Cases_on `x IN FV u` THEN SRW_TAC [][lemma14b] THEN METIS_TAC [],
    METIS_TAC []
  ]);

val FV_SUB = store_thm(
  "FV_SUB",
  ``!t u v. FV ([t/v] u) = if v IN FV u then FV t UNION (FV u DELETE v)
                           else FV u``,
  PROVE_TAC [lemma14b, lemma14c]);

val lemma15a = store_thm(
  "lemma15a",
  ``!M. ~(v IN FV M) ==> ([N/v]([VAR v/x]M) = [N/x]M)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{x;v} UNION FV N` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val lemma15b = store_thm(
  "lemma15b",
  ``~(v IN FV M) ==> ([VAR u/v]([VAR v/u] M) = M)``,
  SRW_TAC [][lemma15a]);

(* ----------------------------------------------------------------------
    alpha-convertibility results
   ---------------------------------------------------------------------- *)

val SIMPLE_ALPHA = store_thm(
  "SIMPLE_ALPHA",
  ``~(y IN FV u) ==> !x. LAM x u = LAM y ([VAR y/x] u)``,
  SRW_TAC [][GSYM fresh_tpm_subst] THEN
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, tpm_flip_args]);


(* ----------------------------------------------------------------------
    size function
   ---------------------------------------------------------------------- *)

val size_exists =
    tm_recursion
        |> INST_TYPE [alpha |-> ``:num``]
        |> SPEC_ALL
        |> Q.INST [`A` |-> `{}`, `apm` |-> `K I`,
             `vr` |-> `\s. 1`, `ap` |-> `\m n t1 t2. m + n + 1`,
             `lm` |-> `\m v t. m + 1`]
        |> SIMP_RULE (srw_ss()) []

val size_thm = new_specification("size_thm", ["size"], size_exists)
val _ = export_rewrites ["size_thm"]

val size_tpm = Store_Thm(
  "size_tpm",
  ``!t. size (tpm pi t) = size t``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);

(* ----------------------------------------------------------------------
    iterated substitutions (ugh)
   ---------------------------------------------------------------------- *)

val ISUB_def =
 Define
     `($ISUB t [] = t)
  /\  ($ISUB t ((s,x)::rst) = $ISUB ([s/x]t) rst)`;

val _ = set_fixity "ISUB" (Infixr 501);

val DOM_DEF =
 Define
     `(DOM [] = {})
  /\  (DOM ((x,y)::rst) = {y} UNION DOM rst)`;

val FVS_DEF =
 Define
    `(FVS [] = {})
 /\  (FVS ((t,x)::rst) = FV t UNION FVS rst)`;


val FINITE_DOM = Q.store_thm("FINITE_DOM",
 `!ss. FINITE (DOM ss)`,
Induct THENL [ALL_TAC, Cases]
   THEN RW_TAC std_ss [DOM_DEF, FINITE_EMPTY, FINITE_UNION, FINITE_SING]);
val _ = export_rewrites ["FINITE_DOM"]


val FINITE_FVS = Q.store_thm("FINITE_FVS",
`!ss. FINITE (FVS ss)`,
Induct THENL [ALL_TAC, Cases]
   THEN RW_TAC std_ss [FVS_DEF, FINITE_EMPTY, FINITE_UNION, FINITE_FV]);
val _ = export_rewrites ["FINITE_FVS"]

val ISUB_LAM = store_thm(
  "ISUB_LAM",
  ``!R x. ~(x IN (DOM R UNION FVS R)) ==>
          !t. (LAM x t) ISUB R = LAM x (t ISUB R)``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [ISUB_def, pairTheory.FORALL_PROD,
                           DOM_DEF, FVS_DEF, SUB_THM]);

(* ----------------------------------------------------------------------
    Simultaneous substitution (using a finite map) - much more interesting
   ---------------------------------------------------------------------- *)

val strterm_fmap_supp = store_thm(
  "strterm_fmap_supp",
  ``supp (fmpm lswapstr tpm) fmap =
      FDOM fmap ∪
      supp (setpm tpm) (FRANGE fmap)``,
  SRW_TAC [][fmap_supp]);

val FINITE_strterm_fmap_supp = store_thm(
  "FINITE_strterm_fmap_supp",
  ``FINITE (supp (fmpm lswapstr tpm) fmap)``,
  SRW_TAC [][strterm_fmap_supp, supp_setpm] THEN SRW_TAC [][]);
val _ = export_rewrites ["FINITE_strterm_fmap_supp"]

val lem1 = prove(
  ``∃a. ~(a ∈ supp (fmpm lswapstr tpm) fm)``,
  Q_TAC (NEW_TAC "z") `supp (fmpm lswapstr tpm) fm` THEN
  METIS_TAC []);

val supp_FRANGE = prove(
  ``~(x ∈ supp (setpm tpm) (FRANGE fm)) =
   ∀y. y ∈ FDOM fm ==> ~(x ∈ FV (fm ' y))``,
  SRW_TAC [][supp_setpm, finite_mapTheory.FRANGE_DEF] THEN METIS_TAC []);

fun ex_conj1 thm = let
  val (v,c) = dest_exists (concl thm)
  val c1 = CONJUNCT1 (ASSUME c)
  val fm = mk_exists(v,concl c1)
in
  CHOOSE (v, thm) (EXISTS(fm,v) c1)
end

val lem2 = prove(
  ``u ∉ FDOM f ∧ v ∉ FDOM f ==> (swapstr u v s IN FDOM f <=> s IN FDOM f)``,
  Cases_on `u = s` THEN SRW_TAC [][] THEN Cases_on `v = s` THEN SRW_TAC [][]);

val ssub_exists =
    tm_recursion
        |> INST_TYPE [alpha |-> ``:term``] |> SPEC_ALL
        |> Q.INST [`vr` |-> `\s. if s ∈ FDOM fm then fm ' s else VAR s`,
                   `lm` |-> `\r v t. LAM v r`, `apm` |-> `tpm`,
                   `ap` |-> `\r1 r2 t1 t2. r1 @@ r2`,
                   `A` |-> `supp (fmpm lswapstr tpm) fm`]
        |> SIMP_RULE (srw_ss()) [tpm_COND, strterm_fmap_supp, lem2,
                                 FAPPLY_eqv_lswapstr, supp_fresh]
        |> Q.GEN `fm`
        |> SIMP_RULE (srw_ss()) [SKOLEM_THM, FORALL_AND_THM, supp_FRANGE]
        |> ex_conj1

val ssub_def = new_specification ("ssub_def", ["ssub"], ssub_exists)
val _ = export_rewrites ["ssub_def"]

val _ = overload_on ("'", ``ssub``)

val tpm_ssub = store_thm(
  "tpm_ssub",
  ``∀t. tpm pi (fm ' t) = fmpm lswapstr tpm pi fm ' (tpm pi t)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `supp (fmpm lswapstr tpm) fm` THEN
  SRW_TAC [][fmpm_FDOM, strterm_fmap_supp, supp_FRANGE] THENL [
    SRW_TAC [][fmpm_applied],
    SRW_TAC [][fmpm_FDOM, fmpm_applied]
  ]);

val single_ssub = store_thm(
  "single_ssub",
  ``∀N. (FEMPTY |+ (s,M)) ' N = [M/s]N``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `s INSERT FV M` THEN
  SRW_TAC [][SUB_VAR, SUB_THM]);

val in_fmap_supp = store_thm(
  "in_fmap_supp",
  ``x ∈ supp (fmpm lswapstr tpm) fm =
      x ∈ FDOM fm ∨
      ∃y. y ∈ FDOM fm ∧ x ∈ FV (fm ' y)``,
  SRW_TAC [][strterm_fmap_supp, nomsetTheory.supp_setpm] THEN
  SRW_TAC [boolSimps.DNF_ss][finite_mapTheory.FRANGE_DEF] THEN METIS_TAC []);

val not_in_fmap_supp = store_thm(
  "not_in_fmap_supp",
  ``~(x ∈ supp (fmpm lswapstr tpm) fm) =
      ~(x ∈ FDOM fm) ∧ ∀y. y ∈ FDOM fm ==> ~(x ∈ FV (fm ' y))``,
  METIS_TAC [in_fmap_supp]);
val _ = export_rewrites ["not_in_fmap_supp"]

val ssub_14b = store_thm(
  "ssub_14b",
  ``∀t. (FV t ∩ FDOM phi = EMPTY) ==> ((phi : string |-> term) ' t = t)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `supp (fmpm lswapstr tpm) phi` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, pred_setTheory.EXTENSION] THEN METIS_TAC []);

val ssub_value = store_thm(
  "ssub_value",
  ``(FV t = EMPTY) ==> ((phi : string |-> term) ' t = t)``,
  SRW_TAC [][ssub_14b]);

val ssub_FEMPTY = store_thm(
  "ssub_FEMPTY",
  ``∀t. FEMPTY ' t = t``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);
val _ = export_rewrites ["ssub_FEMPTY"]


(* ----------------------------------------------------------------------
    Set up the recursion functionality in binderLib
   ---------------------------------------------------------------------- *)

val lemma = prove(
  ``is_perm apm ==>
    ((∀x y t. h (tpm [(x,y)] t) = apm [(x,y)] (h t)) =
     ∀pi t. h (tpm pi t) = apm pi (h t))``,
  strip_tac >> simp_tac (srw_ss()) [EQ_IMP_THM] >> strip_tac >>
  Induct_on `pi` >>
  asm_simp_tac (srw_ss()) [is_perm_nil, pairTheory.FORALL_PROD] >>
  srw_tac [][Once tpm_CONS] >> srw_tac [][GSYM is_perm_decompose]);

val tm_recursion_nosideset = save_thm(
  "tm_recursion_nosideset",
  tm_recursion |> Q.INST [`A` |-> `{}`] |> SIMP_RULE (srw_ss()) [lemma])

val term_info_string =
    "local\n\
    \fun k |-> v = {redex = k, residue = v}\n\
    \open binderLib\n\
    \val term_info = \n\
    \   NTI {nullfv = ``LAM \"\" (VAR \"\")``,\n\
    \        pm_rewrites = [],\n\
    \        pm_constant = ``term$tpm``,\n\
    \        fv_constant = ``term$FV``,\n\
    \        fv_rewrites = [],\n\
    \        recursion_thm = SOME tm_recursion_nosideset,\n\
    \        binders = [(``term$LAM``, 0, tpm_ALPHA)]}\n\
    \val _ = binderLib.type_db :=\n\
    \          Binarymap.insert(!binderLib.type_db,\n\
    \                           {Name = \"term\",Thy=\"term\"},\n\
    \                           term_info)\n\
    \in end;\n"

val _ = adjoin_to_theory
        { sig_ps = NONE,
          struct_ps =
          SOME (fn pps => PP.add_string pps term_info_string)}


val _ = export_theory()



