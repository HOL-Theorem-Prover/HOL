(* this is an -*- sml -*- file *)
open HolKernel Parse boolLib

open BasicProvers
open bossLib binderLib
open pretermTheory basic_swapTheory nomsetTheory
open pred_setTheory
open lcsymtacs
open boolSimps

fun Store_Thm(s, t, tac) = (store_thm(s,t,tac) before export_rewrites [s])
fun Save_Thm(s, th) = (save_thm(s, th) before export_rewrites [s])

val _ = new_theory "term"
(* perform quotient *)

val psize_def = Define`
  (psize (var s) = 1) ∧
  (psize (app t1 t2) = psize t1 + psize t2 + 1) ∧
  (psize (lam v t) = psize t + 1)
`

val psize_ptpm = prove(
  ``psize (ptpm [(x,y)] t) = psize t``,
  Induct_on `t` THEN SRW_TAC [][psize_def]);

val aeq_psize = prove(
  ``∀t1 t2. aeq t1 t2 ==> (psize t1 = psize t2)``,
  Induct_on `aeq` THEN SRW_TAC [][psize_def, psize_ptpm]);

fun mk_def(s,t) =
    {def_name = s ^ "_def", fixity = Prefix, fname = s, func = t};
val app_respects_aeq = List.nth(CONJUNCTS aeq_rules, 1)

val ptpm_fv' = (CONV_RULE (BINDER_CONV
                             (RAND_CONV (SIMP_CONV (srw_ss()) [perm_IN]))) o
                REWRITE_RULE [EXTENSION]) ptpm_fv

val [FV_thm, FV_tpm, simple_induction, tpm_thm, term_distinct, term_11,
     LAM_eq_thm, FRESH_swap0,
     FINITE_FV,
     tpm_sing_inv, tpm_NIL, tpm_inverse, tpm_flip_args, tpm_id_front,
     tmsize_def, tpm_tmsize] =
    quotient.define_equivalence_type
    {
     name = "term", equiv = aeq_equiv,
     defs = map mk_def [("LAM", ``lam``), ("@@", ``app``),
                        ("VAR", ``var``), ("FV", ``fv``),
                        ("tpm", ``ptpm``), ("tmsize", ``psize``)],
     welldefs = [lam_respects_aeq, app_respects_aeq, var_respects_aeq, aeq_fv,
                 SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] aeq_ptpm_lemma,
                 aeq_psize
                 ],
     old_thms = [fv_def, ptpm_fv',
                 TypeBase.induction_of ``:preterm$preterm``, ptpm_def,
                 aeq_distinct, aeq_ptm_11,
                 lam_aeq_thm, fresh_swap, (* ptpm_is_perm,*)
                 finite_fv,
                 ptpm_sing_inv, ptpm_NIL, ptpm_INVERSE, ptpm_flip_args,
                 ptpm_id_front, psize_def, psize_ptpm]}
val _ = set_fixity "@@" (Infixl 901);
val _ = set_MLname "@@_def" "APP_def"

(* hide all of preterm's constants *)
val _ = List.app (fn s => remove_ovl_mapping s {Name = s, Thy = "preterm"})
                 ["fv", "var", "app", "lam", "ptpm", "aeq"]

val _ = remove_ovl_mapping "psize" {Name = "psize", Thy = "term"}

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

val _ = augment_srw_ss [rewrites [tmsize_def, tpm_tmsize]]

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

val FORALL_TERM = store_thm(
  "FORALL_TERM",
  ``(∀t. P t) <=>
      (∀s. P (VAR s)) ∧ (∀t1 t2. P (t1 @@ t2)) ∧ (∀v t. P (LAM v t))``,
  EQ_TAC THEN SRW_TAC [][] THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN SRW_TAC [][]);

val some_PAIR_EQ = prove(
  ``(some (x,y). (x' = x) /\ (y' = y)) = SOME(x',y')``,
  DEEP_INTRO_TAC optionTheory.some_intro THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD]);

val some_PAIR_F = prove(
  ``(some (x,y). F) = NONE``,
  DEEP_INTRO_TAC optionTheory.some_intro THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD]);

val _ = set_fixity "=" (Infix(NONASSOC, 450))
val trec = ``tmrec (A:string set) (ppm: 'p pm) (vf : string -> 'p -> α)
                   (af : ('p -> α) -> ('p -> α) -> term -> term -> 'p -> α)
                   (lf : string -> ('p -> α) -> term -> 'p -> α) : term -> 'p -> α``

val tmrec_defn = Hol_defn "tmrec" `
  ^trec t p =
      case some s. t = VAR s of
        SOME s -> vf s p :α
     || NONE -> (case some (t1,t2). t = t1 @@ t2 of
                    SOME (t1,t2) -> af (^trec t1) (^trec t2) t1 t2 p
                 || NONE ->
                   (case some (v,t0). t = LAM v t0 ∧ v ∉ supp ppm p ∧ v ∉ A of
                       NONE -> ARB
                    || SOME(v,t0) -> lf v (^trec t0) t0 p))
`

val (tmrec_def, tmrec_ind) = Defn.tprove(
  tmrec_defn,
  WF_REL_TAC `measure (tmsize o FST o SND o SND o SND o SND o SND)` THEN
  SRW_TAC [][] THENL [
    Q.SPEC_THEN `t` FULL_STRUCT_CASES_TAC term_CASES THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [some_PAIR_EQ, some_PAIR_F],
    Q.SPEC_THEN `t` FULL_STRUCT_CASES_TAC term_CASES THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [some_PAIR_EQ, some_PAIR_F],
    Q.SPEC_THEN `t` FULL_STRUCT_CASES_TAC term_CASES THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)
                  [some_PAIR_EQ, some_PAIR_F, LAM_eq_thm] THEN
    POP_ASSUM MP_TAC THEN DEEP_INTRO_TAC optionTheory.some_intro THEN
    SIMP_TAC (srw_ss()) [pairTheory.EXISTS_PROD, pairTheory.FORALL_PROD] THEN
    SRW_TAC [][] THEN SRW_TAC [ARITH_ss][]
  ]);

val _ = temp_overload_on ("→", ``fnpm``)
val _ = temp_set_fixity "→" (Infixr 700)

val eqv_helpers =
``(∀x y s p:'p. x ∉ A ∧ y ∉ A ==>
             apm [(x,y)] (vf s p: 'a) = vf (swapstr x y s) (ppm [(x,y)] p)) ∧
  (∀x y t1 t2 r1 r2 p.
     x ∉ A ∧ y ∉ A ∧
     (∀x p. x ∉ A ∧ x ∉ FV t1 ∧ x ∉ supp ppm p ==> x ∉ supp apm (r1 p)) ∧
     (∀x p. x ∉ A ∧ x ∉ FV t2 ∧ x ∉ supp ppm p ==> x ∉ supp apm (r2 p)) ==>
     apm [(x,y)] (af r1 r2 t1 t2 p) =
       af ((ppm → apm) [(x,y)] r1) ((ppm→apm) [(x,y)] r2)
          (tpm [(x,y)] t1) (tpm [(x,y)] t2)
          (ppm [(x,y)] p))
     ∧
  (∀x y v t r p.
     x ∉ A ∧ y ∉ A ∧ v ∉ A ∧ v ∉ supp ppm p ∧
     (∀x p. x ∉ A ∧ x ∉ FV t ∧ x ∉ supp ppm p ==> x ∉ supp apm (r p)) ==>
     apm [(x,y)] (lf v r t p) =
       lf (swapstr x y v) ((ppm→apm) [(x,y)] r) (tpm [(x,y)] t) (ppm [(x,y)] p))``

val FCB =
  ``∀a r t:term p:'p.
      a ∉ A ∧ (∀x p:'p. x ∉ A ∧ x ∉ FV t ∧ x ∉ supp ppm p ==> x ∉ supp apm (r p)) ==>
      a ∉ supp apm (lf a r t p:α)``

val notinsupp_I = prove(
  ``∀A apm e x.
       is_perm apm ∧ FINITE A ∧ support apm x A ∧ e ∉ A ==> e ∉ supp apm x``,
  metis_tac [supp_smallest, SUBSET_DEF]);


val tmrec_VAR = tmrec_def |> Q.INST [`t` |-> `VAR s`]
                          |> SIMP_RULE (srw_ss()) []
val tmrec_APP = tmrec_def |> Q.INST [`t` |-> `t1 @@ t2`]
                          |> SIMP_RULE (srw_ss() ++ ETA_ss) [some_PAIR_EQ]

val tmrec_LAM = tmrec_def |> Q.INST [`t` |-> `LAM v t`]
                          |> SIMP_RULE (srw_ss()) [some_PAIR_EQ, some_PAIR_F]

val trec_fnpm = prove(
  ``(ppm → apm) π (tmrec A ppm vf af lf t) =
    λp. apm π (tmrec A ppm vf af lf t (ppm π⁻¹ p))``,
  srw_tac [][FUN_EQ_THM, fnpm_def]);

val tmrec_eqvfresh = prove(
  ``FINITE A ∧ is_perm apm ∧ is_perm ppm ∧ (∀p. FINITE (supp ppm p)) ∧
    ^eqv_helpers ∧ ^FCB ==>
    ∀t.
       (∀p x y. x ∉ A ∧ y ∉ A ==>
                apm [(x,y)] (tmrec A ppm vf af lf t p) =
                 tmrec A ppm vf af lf (tpm [(x,y)] t) (ppm [(x,y)] p)) ∧
       (∀p x. x ∉ A ∧ x ∉ FV t ∧ x ∉ supp ppm p ==>
              x ∉ supp apm (tmrec A ppm vf af lf t p))``,
  strip_tac >> gen_tac >> completeInduct_on `tmsize t` >>
  qabbrev_tac `m = v` >> markerLib.RM_ALL_ABBREVS_TAC >>
  pop_assum (strip_assume_tac o SIMP_RULE (srw_ss() ++ DNF_ss) []) >>
  simp_tac (srw_ss()) [Once FORALL_TERM] >> srw_tac [][tmrec_VAR, tmrec_APP] >| [
    match_mp_tac notinsupp_I >> qexists_tac `A ∪ {s} ∪ supp ppm p` >>
    srw_tac [][support_def, supp_fresh],
    srw_tac [ARITH_ss, ETA_ss][trec_fnpm, is_perm_sing_inv],
    match_mp_tac notinsupp_I >> qexists_tac `FV t1 ∪ FV t2 ∪ A ∪ supp ppm p` >>
    srw_tac [ARITH_ss, ETA_ss][support_def, trec_fnpm, is_perm_sing_inv, supp_fresh,
                               tpm_fresh],
    srw_tac [][tmrec_LAM, SimpLHS] >> DEEP_INTRO_TAC optionTheory.some_intro >>
    simp_tac (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
    REVERSE conj_tac >-
      (srw_tac [][LAM_eq_thm] >>
       Q_TAC (NEW_TAC "z") `A ∪ supp ppm p ∪ {v} ∪ FV t` >>
       first_x_assum (qspec_then `z` mp_tac) >>
       asm_simp_tac (srw_ss()) [tpm_eqr]) >>
    asm_simp_tac (srw_ss() ++ DNF_ss ++ ETA_ss)
                 [LAM_eq_thm, trec_fnpm, is_perm_sing_inv] >>
    asm_simp_tac (srw_ss()) [tpm_eqr] >> conj_tac >-
      (srw_tac [][tmrec_LAM] >> DEEP_INTRO_TAC optionTheory.some_intro >>
       simp_tac (srw_ss()) [pairTheory.EXISTS_PROD, pairTheory.FORALL_PROD] >>
       REVERSE conj_tac >-
         (srw_tac [][LAM_eq_thm]>>
          Q_TAC (NEW_TAC "z")
            `A ∪ supp ppm (ppm [(x,y)] p) ∪ {swapstr x y v} ∪ FV (tpm [(x,y)] t)` >>
          first_x_assum (qspec_then `z` mp_tac) >>
          asm_simp_tac (srw_ss()) [tpm_eqr] >> full_simp_tac (srw_ss()) []) >>
       asm_simp_tac (srw_ss() ++ DNF_ss ++ ETA_ss)
                    [LAM_eq_thm, tpm_eqr] >>
       qx_gen_tac `u` >> qabbrev_tac `w = swapstr x y v` >>
       `w ∉ A ∧ swapstr x y w = v ∧ w ∉ supp ppm (ppm [(x,y)] p)`
         by (srw_tac [][Abbr`w`, perm_supp] >> srw_tac [][swapstr_def]) >>
       `∀p x y. x ∉ A ∧ y ∉ A ==>
                apm [(x,y)] (tmrec A ppm vf af lf t p) =
                  tmrec A ppm vf af lf (tpm [(x,y)] t) (ppm [(x,y)] p)`
          by srw_tac [ARITH_ss][] >>
       `∀a p. a ∉ A ==> a ∉ supp apm (lf a (tmrec A ppm vf af lf t) t p)`
          by srw_tac [][] >>
       strip_tac >>
       `u ∉ supp apm (lf w (tmrec A ppm vf af lf (tpm [(x,y)] t)) (tpm [(x,y)] t)
                         (ppm [(x,y)] p))`
         by (match_mp_tac notinsupp_I >>
             qexists_tac `A ∪ supp ppm (ppm [(x,y)] p) ∪ {w} ∪ FV (tpm [(x,y)] t)` >>
             asm_simp_tac (srw_ss() ++ ETA_ss)
                [support_def, perm_supp, trec_fnpm, tpm_fresh,
                 supp_fresh, is_perm_sing_inv]) >>
       qmatch_abbrev_tac `LHS = RHS` >>
       `RHS = apm [(w,u)] LHS`
          by asm_simp_tac (srw_ss() ++ ETA_ss)
                [Abbr`LHS`, Abbr`RHS`, trec_fnpm, is_perm_sing_inv, tpm_fresh,
                 supp_fresh] >>
       `_ = LHS`
         by (match_mp_tac supp_fresh >>
             asm_simp_tac (srw_ss()) [Abbr`LHS`, Abbr`RHS`]) >>
       srw_tac [][]) >>
    qx_gen_tac `u` >> strip_tac >>
    asm_simp_tac (srw_ss()) [tmrec_LAM] >>
    DEEP_INTRO_TAC optionTheory.some_intro >>
    asm_simp_tac (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
    REVERSE conj_tac >-
      (asm_simp_tac (srw_ss()) [LAM_eq_thm] >>
       Q_TAC (NEW_TAC "z")
         `{swapstr x y v} ∪ A ∪ supp ppm (ppm [(x,y)] p) ∪ FV (tpm [(x,y)] t)` >>
       disch_then (qspec_then `z` mp_tac) >>
       asm_simp_tac (srw_ss()) [tpm_eqr] >> full_simp_tac (srw_ss()) []) >>
    asm_simp_tac (srw_ss() ++ DNF_ss ++ ETA_ss) [LAM_eq_thm, tpm_eqr, perm_supp] >>
    conj_tac >-
      (strip_tac >> qmatch_abbrev_tac `LHS = RHS` >>
       `v ∉ A` by (full_simp_tac (srw_ss()) [swapstr_def] >> metis_tac []) >>
       `RHS = apm [(x,y)] (lf v (tmrec A ppm vf af lf t) t p)`
          by asm_simp_tac (srw_ss() ++ ARITH_ss ++ ETA_ss)
                          [Abbr`RHS`, trec_fnpm, is_perm_sing_inv] >>
       `LHS =
         apm [(x,y)] (lf u (tmrec A ppm vf af lf (tpm [(v,u)] t)) (tpm [(v,u)] t) p)`
          by asm_simp_tac (srw_ss() ++ ARITH_ss ++ ETA_ss)
                          [Abbr`RHS`, trec_fnpm, is_perm_sing_inv] >>
       NTAC 2 (pop_assum SUBST1_TAC) >>
       asm_simp_tac (srw_ss()) [is_perm_injective] >>
       markerLib.RM_ALL_ABBREVS_TAC >>
       qmatch_abbrev_tac `LHS = RHS` >>
       `LHS = apm [(v,u)] RHS`
         by asm_simp_tac (srw_ss() ++ ETA_ss) [Abbr`LHS`, Abbr`RHS`, trec_fnpm,
                                               is_perm_sing_inv, supp_fresh] >>
       pop_assum SUBST1_TAC >>
       match_mp_tac supp_fresh >> qunabbrev_tac `RHS` >>
       markerLib.RM_ALL_ABBREVS_TAC >> srw_tac [][] >>
       match_mp_tac notinsupp_I >> qexists_tac `A ∪ supp ppm p ∪ FV t ∪ {v}` >>
       srw_tac [ETA_ss][support_def, trec_fnpm, is_perm_sing_inv, supp_fresh,
                        tpm_fresh]) >>
   qx_gen_tac `w` >> strip_tac >>
   qmatch_abbrev_tac `LHS = RHS` >>
   `swapstr x y w ∉ A` by srw_tac [][swapstr_def] >>
   `LHS = apm [(x,y)] (lf u (tmrec A ppm vf af lf (tpm [(v,u)] t)) (tpm [(v,u)] t) p)`
      by asm_simp_tac (srw_ss() ++ ARITH_ss ++ ETA_ss)
                      [trec_fnpm, is_perm_sing_inv] >>
   `RHS = apm [(x,y)] (lf (swapstr x y w)
                          (tmrec A ppm vf af lf (tpm [(v, swapstr x y w)] t))
                          (tpm [(v, swapstr x y w)] t) p)`
      by (asm_simp_tac (srw_ss() ++ ARITH_ss ++ ETA_ss)
                       [trec_fnpm, is_perm_sing_inv] >>
          ONCE_REWRITE_TAC [GSYM tpm_sing_to_back] >>
          asm_simp_tac (srw_ss()) []) >>
   NTAC 2 (POP_ASSUM SUBST1_TAC) >>
   asm_simp_tac (srw_ss()) [is_perm_injective] >>
   markerLib.RM_ALL_ABBREVS_TAC >>
   qmatch_abbrev_tac `LHS = RHS` >>
   `swapstr x y w ≠ v` by srw_tac [][swapstr_eq_left] >>
   `LHS = apm [(swapstr x y w, u)] RHS`
     by (asm_simp_tac (srw_ss() ++ ARITH_ss ++ ETA_ss)
                      [Abbr`RHS`, trec_fnpm, is_perm_sing_inv, supp_fresh] >>
         ONCE_REWRITE_TAC [GSYM tpm_sing_to_back] >>
         asm_simp_tac (srw_ss()) [tpm_fresh]) >>
   pop_assum SUBST1_TAC >>
   Cases_on `u = swapstr x y w` >- srw_tac [][is_perm_id, is_perm_nil] >>
   match_mp_tac supp_fresh >>
   srw_tac [ARITH_ss][Abbr`LHS`, Abbr`RHS`] >>
   match_mp_tac notinsupp_I >>
   qexists_tac `A ∪ {v; swapstr x y w} ∪ FV t ∪ supp ppm p` >>
   srw_tac [ETA_ss][support_def, trec_fnpm, tpm_fresh, is_perm_sing_inv, supp_fresh],


   asm_simp_tac (srw_ss()) [tmrec_LAM] >> DEEP_INTRO_TAC optionTheory.some_intro >>
   asm_simp_tac (srw_ss()) [pairTheory.EXISTS_PROD, pairTheory.FORALL_PROD] >>
   REVERSE conj_tac >-
     (asm_simp_tac (srw_ss()) [LAM_eq_thm] >>
      Q_TAC (NEW_TAC "z") `supp ppm p ∪ A ∪ FV t ∪ {v}` >>
      disch_then (qspec_then `z` mp_tac) >> srw_tac [][tpm_eqr]) >>
   asm_simp_tac (srw_ss() ++ DNF_ss ++ ETA_ss) [LAM_eq_thm] >>
   conj_tac >-
     (strip_tac >> Cases_on `x = v` >- srw_tac [ARITH_ss][] >>
      `x ∉ FV t` by srw_tac [][] >>
      match_mp_tac notinsupp_I >> qexists_tac `A ∪ {v} ∪ FV t ∪ supp ppm p` >>
      srw_tac [ETA_ss][support_def, trec_fnpm, supp_fresh, is_perm_sing_inv,
                       tpm_fresh]) >>
   asm_simp_tac (srw_ss()) [tpm_eqr] >>
   qx_gen_tac `u` >> strip_tac >>
   Cases_on `x = u` >- srw_tac [ARITH_ss][] >>
   Cases_on `x = v` >| [
     srw_tac [][] >> qmatch_abbrev_tac `v ∉ supp apm LFT` >>
     `LFT = apm [(v,u)] (lf v (tmrec A ppm vf af lf t) t p)`
        by srw_tac [ETA_ss][trec_fnpm, supp_fresh, is_perm_sing_inv] >>
     pop_assum SUBST1_TAC >>
     srw_tac [][perm_supp] >>
     match_mp_tac notinsupp_I >>
     qexists_tac `A ∪ supp ppm p ∪ {v} ∪ FV t` >>
     srw_tac [ETA_ss][support_def, supp_fresh, trec_fnpm, is_perm_sing_inv, tpm_fresh],
     `x ∉ FV t` by srw_tac [][] >>
     match_mp_tac notinsupp_I >>
     qexists_tac `A ∪ supp ppm p ∪ {u;v} ∪ FV t` >>
     srw_tac [ETA_ss][support_def, supp_fresh, trec_fnpm, is_perm_sing_inv, tpm_fresh]
   ]
  ]);

fun udplus th =
    th |> REWRITE_RULE [GSYM CONJ_ASSOC]
       |> repeat (UNDISCH o CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)))
       |> UNDISCH

val eqvfresh_I = tmrec_eqvfresh |> udplus
                                |> SIMP_RULE (srw_ss()) [FORALL_AND_THM]

val parameter_tm_recursion = store_thm(
  "parameter_tm_recursion",
  ``FINITE A ∧ is_perm apm ∧ ^eqv_helpers ∧ ^FCB ∧ is_perm ppm ∧
    (∀p. FINITE (supp ppm p)) ==>
    ∃f. ((∀s p. f (VAR s) p = vf s p) ∧
         (∀t1 t2 p. f (t1 @@ t2) p = af (f t1) (f t2) t1 t2 p) ∧
         (∀v t p. v ∉ A ∧ v ∉ supp ppm p ==>
                    f (LAM v t) p = lf v (f t) t p)) ∧
        ∀x y t p. x ∉ A ∧ y ∉ A ==>
                   apm [(x,y)] (f t p) = f (tpm [(x,y)] t) (ppm [(x,y)] p)``,
  strip_tac >> qexists_tac `tmrec A ppm vf af lf` >>
  srw_tac [][tmrec_VAR, tmrec_APP] >| [
    srw_tac [][tmrec_LAM] >>
    DEEP_INTRO_TAC optionTheory.some_intro >>
    asm_simp_tac (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
    REVERSE conj_tac
      >- (asm_simp_tac (srw_ss()) [LAM_eq_thm] >>
          Q_TAC (NEW_TAC "z") `A ∪ supp ppm p ∪ FV t ∪ {v}` >>
          disch_then (qspec_then `z` mp_tac) >>
          srw_tac [][tpm_eqr]) >>
    asm_simp_tac (srw_ss() ++ DNF_ss ++ ETA_ss) [LAM_eq_thm, tpm_eqr] >>
    qx_gen_tac `u` >> rpt strip_tac >>
    qmatch_abbrev_tac `LHS = RHS` >>
    `LHS = apm [(v,u)] RHS`
      by asm_simp_tac (srw_ss() ++ ETA_ss)
                      [Abbr`RHS`, eqvfresh_I, trec_fnpm, is_perm_sing_inv,
                       supp_fresh] >>
    pop_assum SUBST1_TAC >>
    match_mp_tac supp_fresh >>
    srw_tac [][Abbr`LHS`, Abbr`RHS`, eqvfresh_I] >>
    match_mp_tac notinsupp_I >>
    qexists_tac `A ∪ FV t ∪ {v} ∪ supp ppm p` >>
    srw_tac [ETA_ss][eqvfresh_I, support_def, trec_fnpm, is_perm_sing_inv, supp_fresh,
                     tpm_fresh],
    srw_tac [][eqvfresh_I]
  ]);

val FORALL_ONE = prove(
  ``(!u:one. P u) = P ()``,
  SRW_TAC [][EQ_IMP_THM, oneTheory.one_induction]);
val FORALL_ONE_FN = prove(
  ``(!uf : one -> 'a. P uf) = !a. P (\u. a)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  POP_ASSUM (Q.SPEC_THEN `uf ()` MP_TAC) THEN
  Q_TAC SUFF_TAC `(\y. uf()) = uf` THEN1 SRW_TAC [][] THEN
  SRW_TAC [][FUN_EQ_THM, oneTheory.one]);

val EXISTS_ONE_FN = prove(
  ``(?f : 'a -> one -> 'b. P f) = (?f : 'a -> 'b. P (\x u. f x))``,
  SRW_TAC [][EQ_IMP_THM] THENL [
    Q.EXISTS_TAC `\a. f a ()` THEN SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `(\x u. f x ()) = f` THEN1 SRW_TAC [][] THEN
    SRW_TAC [][FUN_EQ_THM, oneTheory.one],
    Q.EXISTS_TAC `\a u. f a` THEN SRW_TAC [][]
  ]);

val tm_recursion = save_thm(
  "tm_recursion",
  parameter_tm_recursion
      |> INST_TYPE [``:'p`` |-> ``:unit``]
      |> Q.INST [`vf` |-> `λs u. vr s`,
                 `af` |-> `λr1 r2 t1 t2 u. ap (r1 ()) (r2 ()) t1 t2`,
                 `lf` |-> `λv r t u. lm (r()) v t`,
                 `ppm` |-> `K I : unit pm`]
      |> SIMP_RULE (srw_ss()) [FORALL_ONE, FORALL_ONE_FN, fnpm_def, EXISTS_ONE_FN])

val _ = app delete_const ["tmsize", "tmrec"]

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
  ``x ∈ supp (fmpm lswapstr tpm) fm <=>
      x ∈ FDOM fm ∨
      ∃y. y ∈ FDOM fm ∧ x ∈ FV (fm ' y)``,
  SRW_TAC [][strterm_fmap_supp, nomsetTheory.supp_setpm] THEN
  SRW_TAC [boolSimps.DNF_ss][finite_mapTheory.FRANGE_DEF] THEN METIS_TAC []);

val not_in_fmap_supp = store_thm(
  "not_in_fmap_supp",
  ``x ∉ supp (fmpm lswapstr tpm) fm <=>
      x ∉ FDOM fm ∧ ∀y. y ∈ FDOM fm ==> x ∉ FV (fm ' y)``,
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
    ((∀x y t. apm [(x,y)] (h t) = h (tpm [(x,y)] t)) <=>
     ∀pi t. apm pi (h t) = h (tpm pi t))``,
  strip_tac >> simp_tac (srw_ss()) [EQ_IMP_THM] >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
  strip_tac >> Induct_on `pi` >>
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



