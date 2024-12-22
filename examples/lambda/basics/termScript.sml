(* ========================================================================== *)
(* FILE    : termScript.sml                                                   *)
(* TITLE   : The type of Lambda terms and its substitution operations         *)
(*                                                                            *)
(* AUTHORS : 2005-2011 Michael Norrish                                        *)
(*         : 2023-2024 Michael Norrish and Chun Tian                          *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open boolSimps arithmeticTheory pred_setTheory listTheory finite_mapTheory
     relationTheory pairTheory hurdUtils rich_listTheory;

open generic_termsTheory binderLib nomsetTheory nomdatatype;

val _ = new_theory "term";

val _ = set_fixity "=" (Infix(NONASSOC, 450))

val tyname = "term"

val vp = “(λn u:unit. n = 0)”
val lp = “(λn (d:unit + unit) tns uns.
               (n = 0) ∧ ISL d ∧ (tns = []) ∧ (uns = [0;0]) ∨
               (n = 0) ∧ ISR d ∧ (tns = [0]) ∧ (uns = []))”

val {term_ABS_pseudo11, term_REP_11, genind_term_REP, genind_exists,
     termP, absrep_id, repabs_pseudo_id, term_REP_t, term_ABS_t, newty, ...} =
    new_type_step1 tyname 0 {vp = vp, lp = lp};

val [gvar,glam] = genind_rules |> SPEC_ALL |> CONJUNCTS

val LAM_t = mk_var("LAM", ``:string -> ^newty -> ^newty``)
val LAM_def = new_definition(
  "LAM_def",
  ``^LAM_t v t = ^term_ABS_t (GLAM v (INR ()) [^term_REP_t t] [])``);

val LAM_termP = prove(
  mk_comb(termP, LAM_def |> SPEC_ALL |> concl |> rhs |> rand),
  match_mp_tac glam >> srw_tac [][genind_term_REP]);
val LAM_t = defined_const LAM_def

val APP_t = mk_var("APP", ``:^newty -> ^newty -> ^newty``)
val APP_def = new_definition(
  "APP_def",
  ``^APP_t t1 t2 =
       ^term_ABS_t (GLAM ARB (INL ()) [] [^term_REP_t t1; ^term_REP_t t2])``);
val APP_termP = prove(
  ``^termP (GLAM x (INL ()) [] [^term_REP_t t1; ^term_REP_t t2])``,
  match_mp_tac glam >> srw_tac [][genind_term_REP])
val APP_t = defined_const APP_def

val APP_def' = prove(
  ``^term_ABS_t (GLAM v (INL ()) [] [^term_REP_t t1; ^term_REP_t t2]) = ^APP_t t1 t2``,
  srw_tac [][APP_def, GLAM_NIL_EQ, term_ABS_pseudo11, APP_termP]);

val VAR_t = mk_var("VAR", ``:string -> ^newty``)
val VAR_def = new_definition(
  "VAR_def",
  ``^VAR_t s = ^term_ABS_t (GVAR s ())``);
val VAR_termP = prove(
  mk_comb(termP, VAR_def |> SPEC_ALL |> concl |> rhs |> rand),
  srw_tac [][genind_rules]);
val VAR_t = defined_const VAR_def

val cons_info =
    [{con_termP = VAR_termP, con_def = VAR_def},
     {con_termP = APP_termP, con_def = SYM APP_def'},
     {con_termP = LAM_termP, con_def = LAM_def}]

(* tpm *)
val tpm_name_pfx = "t"
val {tpm_thm, term_REP_tpm, t_pmact_t, tpm_t} =
    define_permutation {name_pfx = "t", name = tyname,
                        term_REP_t = term_REP_t,
                        term_ABS_t = term_ABS_t, absrep_id = absrep_id,
                        repabs_pseudo_id = repabs_pseudo_id,
                        cons_info = cons_info, newty = newty,
                        genind_term_REP = genind_term_REP};

(* support *)
val term_REP_eqv = prove(
   ``support (fn_pmact ^t_pmact_t gt_pmact) ^term_REP_t {}`` ,
   srw_tac [][support_def, fnpm_def, FUN_EQ_THM, term_REP_tpm, pmact_sing_inv]);

val supp_term_REP = prove(
  ``supp (fn_pmact ^t_pmact_t gt_pmact) ^term_REP_t = {}``,
  REWRITE_TAC [GSYM SUBSET_EMPTY] >> MATCH_MP_TAC (GEN_ALL supp_smallest) >>
  srw_tac [][term_REP_eqv])

val tpm_def' =
    term_REP_tpm |> AP_TERM term_ABS_t |> PURE_REWRITE_RULE [absrep_id]

val t = mk_var("t", newty)
val supptpm_support = prove(
  ``support ^t_pmact_t ^t (supp gt_pmact (^term_REP_t ^t))``,
  srw_tac [][support_def, tpm_def', supp_fresh, absrep_id]);

val supptpm_apart = prove(
  ``x ∈ supp gt_pmact (^term_REP_t ^t) ∧ y ∉ supp gt_pmact (^term_REP_t ^t) ⇒
    ^tpm_t [(x,y)] ^t ≠ ^t``,
  srw_tac [][tpm_def']>>
  DISCH_THEN (MP_TAC o AP_TERM term_REP_t) >>
  srw_tac [][repabs_pseudo_id, genind_gtpm_eqn, genind_term_REP, supp_apart]);

val supp_tpm = prove(
  ``supp ^t_pmact_t ^t = supp gt_pmact (^term_REP_t ^t)``,
  match_mp_tac (GEN_ALL supp_unique_apart) >>
  srw_tac [][supptpm_support, supptpm_apart, FINITE_GFV])

Overload FV = “supp ^t_pmact_t”

Theorem FINITE_FV[simp]: FINITE (FV t)
Proof srw_tac [][supp_tpm, FINITE_GFV]
QED

Theorem FINITE_BIGUNION_IMAGE_FV[simp] :
    FINITE (BIGUNION (IMAGE FV (set Ns)))
Proof
    rw [] >> rw [FINITE_FV]
QED

fun supp_clause {con_termP, con_def} = let
  val t = mk_comb(``supp ^t_pmact_t``, lhand (concl (SPEC_ALL con_def)))
in
  t |> REWRITE_CONV [supp_tpm, con_def, MATCH_MP repabs_pseudo_id con_termP,
                     GFV_thm]
    |> REWRITE_RULE [supp_listpm, EMPTY_DELETE, UNION_EMPTY]
    |> REWRITE_RULE [GSYM supp_tpm]
    |> GEN_ALL
end

(* |- (!s. FV (VAR s) = {s}) /\ (!t2 t1. FV (t1 @@ t2) = FV t1 UNION FV t2) /\
      !v t. FV (LAM v t) = FV t DELETE v
 *)
Theorem FV_thm[simp] = LIST_CONJ (map supp_clause cons_info)

fun genit th = let
  val (_, args) = strip_comb (concl th)
  val (tm, x) = case args of [x,y] => (x,y) | _ => raise Fail "Bind"
  val ty = type_of tm
  val t = mk_var("t", ty)
in
  th |> INST [tm |-> t] |> GEN x |> GEN t
end

val LIST_REL_CONS1 = listTheory.LIST_REL_CONS1
val LIST_REL_NIL = listTheory.LIST_REL_NIL

val term_ind =
    bvc_genind
        |> INST_TYPE [alpha |-> ``:unit+unit``, beta |-> ``:unit``]
        |> Q.INST [`vp` |-> `^vp`, `lp` |-> `^lp`]
        |> SIMP_RULE std_ss [LIST_REL_CONS1, RIGHT_AND_OVER_OR,
                             LEFT_AND_OVER_OR, DISJ_IMP_THM, LIST_REL_NIL]
        |> Q.SPEC `λn t0 x. Q t0 x`
        |> Q.SPEC `fv`
        |> UNDISCH |> Q.SPEC `0` |> DISCH_ALL
        |> SIMP_RULE (std_ss ++ DNF_ss)
                     [sumTheory.FORALL_SUM, supp_listpm,
                      IN_UNION, NOT_IN_EMPTY, oneTheory.FORALL_ONE,
                      genind_exists, LIST_REL_CONS1, LIST_REL_NIL]
        |> Q.INST [`Q` |-> `λt. P (term_ABS t)`]
        |> SIMP_RULE std_ss [GSYM LAM_def, APP_def', GSYM VAR_def, absrep_id]
        |> SIMP_RULE (srw_ss()) [GSYM supp_tpm]
        |> elim_unnecessary_atoms {finite_fv = FINITE_FV}
                                  [ASSUME ``!x:'c. FINITE (fv x:string set)``]
        |> SPEC_ALL |> UNDISCH
        |> genit |> DISCH_ALL |> Q.GEN `fv` |> Q.GEN `P`

fun mkX_ind th = th |> Q.SPEC `λt x. Q t` |> Q.SPEC `λx. X`
                    |> SIMP_RULE std_ss [] |> Q.GEN `X`
                    |> Q.INST [`Q` |-> `P`] |> Q.GEN `P`

Theorem nc_INDUCTION[local] = mkX_ind term_ind

(* exactly mimic historical bound variable names etc for backwards
   compatibility *)
Theorem nc_INDUCTION2 :
    ∀P X.
      (∀s. P (VAR s)) ∧
      (∀t u. P t ∧ P u ==> P (APP t u)) ∧
      (∀y u. y ∉ X ∧ P u ==> P (LAM y u)) ∧ FINITE X ==>
      ∀u. P u
Proof
  metis_tac [nc_INDUCTION]
QED

val LAM_eq_thm = save_thm(
  "LAM_eq_thm",
  ``(LAM u t1 = LAM v t2)``
     |> SIMP_CONV (srw_ss()) [LAM_def, LAM_termP, term_ABS_pseudo11,
                              GLAM_eq_thm, term_REP_11, GSYM term_REP_tpm,
                              GSYM supp_tpm]
     |> GENL [``u:string``, ``v:string``, ``t1:term``, ``t2:term``]);

val (_, repty) = dom_rng (type_of term_REP_t)
val repty' = ty_antiq repty

val tlf =
   “λ(v:string) (u:unit + unit) (ds1:(ρ -> α) list) (ds2:(ρ -> α) list)
                                (ts1:^repty' list) (ts2:^repty' list) (p :ρ).
       if ISR u then tlf (HD ds1) v (^term_ABS_t (HD ts1)) p :α
       else taf (HD ds2) (HD (TL ds2)) (^term_ABS_t (HD ts2))
                (^term_ABS_t (HD (TL ts2))) p :α”
val tvf = “λ(s:string) (u:unit) (p:ρ). tvf s p :α”;

val termP_elim = prove(
  ``(∀g. ^termP g ⇒ P g) ⇔ (∀t. P (^term_REP_t t))``,
  srw_tac [][EQ_IMP_THM] >- srw_tac [][genind_term_REP] >>
  first_x_assum (qspec_then `^term_ABS_t g` mp_tac) >>
  srw_tac [][repabs_pseudo_id]);

val termP_removal =
    nomdatatype.termP_removal {
      elimth = termP_elim, absrep_id = absrep_id,
      tpm_def = AP_TERM term_ABS_t term_REP_tpm |> REWRITE_RULE [absrep_id],
      termP = termP, repty = repty}

val termP0 = prove(
  ``genind ^vp ^lp n t <=> ^termP t ∧ (n = 0)``,
  EQ_TAC >> simp_tac (srw_ss()) [] >> strip_tac >>
  qsuff_tac `n = 0` >- (strip_tac >> srw_tac [][]) >>
  pop_assum mp_tac >>
  Q.ISPEC_THEN `t` STRUCT_CASES_TAC gterm_cases >>
  srw_tac [][genind_GVAR, genind_GLAM_eqn]);

val parameter_tm_recursion = save_thm(
  "parameter_tm_recursion",
  parameter_gtm_recursion
      |> INST_TYPE [alpha |-> ``:unit + unit``, beta |-> ``:unit``,
                    gamma |-> alpha]
      |> Q.INST [`lf` |-> `^tlf`, `vf` |-> `^tvf`, `vp` |-> `^vp`,
                 `lp` |-> `^lp`, `n` |-> `0`]
      |> SIMP_RULE (srw_ss()) [sumTheory.FORALL_SUM, FORALL_AND_THM,
                               GSYM RIGHT_FORALL_IMP_THM, IMP_CONJ_THM,
                               GSYM RIGHT_EXISTS_AND_THM,
                               GSYM LEFT_EXISTS_AND_THM,
                               GSYM LEFT_FORALL_IMP_THM,
                               LIST_REL_CONS1, genind_GVAR,
                               genind_GLAM_eqn, sidecond_def,
                               NEWFCB_def, relsupp_def,
                               LENGTH_NIL_SYM, LENGTH1, LENGTH2]
      |> ONCE_REWRITE_RULE [termP0]
      |> SIMP_RULE (srw_ss() ++ DNF_ss) [LENGTH1, LENGTH2, LENGTH_NIL]
      |> CONV_RULE (DEPTH_CONV termP_removal)
      |> SIMP_RULE (srw_ss()) [GSYM supp_tpm, SYM term_REP_tpm]
      |> UNDISCH
      |> rpt_hyp_dest_conj
      |> lift_exfunction {repabs_pseudo_id = repabs_pseudo_id,
                          term_REP_t = term_REP_t,
                          cons_info = cons_info}
      |> DISCH_ALL
      |> elim_unnecessary_atoms {finite_fv = FINITE_FV}
                                [ASSUME ``FINITE (A:string set)``,
                                 ASSUME ``!p:ρ. FINITE (supp ppm p)``]
      |> UNDISCH_ALL |> DISCH_ALL
      |> REWRITE_RULE [AND_IMP_INTRO]
      |> CONV_RULE (LAND_CONV (REWRITE_CONV [GSYM CONJ_ASSOC]))
      |> Q.INST [`tvf` |-> `vr`, `tlf` |-> `lm`, `taf` |-> `ap`,
                 `dpm` |-> `apm`]
      |> CONV_RULE (REDEPTH_CONV sort_uvars))

val tm_recursion = save_thm(
  "tm_recursion",
  parameter_tm_recursion
      |> Q.INST_TYPE [`:ρ` |-> `:unit`]
      |> Q.INST [`ppm` |-> `discrete_pmact`, `vr` |-> `λs u. vru s`,
                 `ap` |-> `λr1 r2 t1 t2 u. apu (r1()) (r2()) t1 t2`,
                 `lm` |-> `λr v t u. lmu (r()) v t`]
      |> SIMP_RULE (srw_ss()) [oneTheory.FORALL_ONE, oneTheory.FORALL_ONE_FN,
                               oneTheory.EXISTS_ONE_FN, fnpm_def]
      |> SIMP_RULE (srw_ss() ++ CONJ_ss) [supp_unitfn]
      |> Q.INST [`apu` |-> `ap`, `lmu` |-> `lm`, `vru` |-> `vr`])

(* |- !x t p. x IN FV (tpm p t) <=> lswapstr (REVERSE p) x IN FV t *)
Theorem FV_tpm[simp] = ``x ∈ FV (tpm p t)``
                      |> REWRITE_CONV [perm_supp,pmact_IN]
                      |> GEN_ALL

val _ = set_mapped_fixity { term_name = "APP", tok = "@@",
                            fixity = Infixl 901}

(* NOTE: The following overload "incompatible" was in sttScript.sml.

   The current "incompatibility" is between a (string) variable and a term.
   See chap2Theory for the incompatibility between two terms.
 *)
val _ = set_fixity "#" (Infix(NONASSOC, 450))
Overload "#" = “λv M:term. v ∉ FV M”

Theorem FRESH_APP[simp]: v NOTIN FV (M @@ N) <=> v NOTIN FV M /\ v NOTIN FV N
Proof SRW_TAC [][]
QED

Theorem FRESH_LAM[simp]:
  u NOTIN FV (LAM v M) <=> (u <> v ==> u NOTIN FV M)
Proof SRW_TAC [][] THEN METIS_TAC []
QED

val FV_EMPTY = store_thm(
  "FV_EMPTY",
  ``(FV t = {}) <=> !v. v NOTIN FV t``,
  SIMP_TAC (srw_ss()) [EXTENSION]);

(* A term is "closed" if it's FV is empty (otherwise the term is open).

   NOTE: the set of all closed terms forms $\Lambda_0$ found in textbooks.
 *)
Definition closed_def :
    closed (M :term) <=> FV M = {}
End

(* quote the term in order to get the variable names specified *)
val simple_induction = store_thm(
  "simple_induction",
  ``!P. (!s. P (VAR s)) /\
        (!M N. P M /\ P N ==> P (M @@ N)) /\
        (!v M. P M ==> P (LAM v M)) ==>
        !M. P M``,
  METIS_TAC [nc_INDUCTION2, FINITE_EMPTY, NOT_IN_EMPTY])

Theorem tpm_eqr:
  (t = tpm pi u) = (tpm (REVERSE pi) t = u)
Proof
  METIS_TAC [pmact_inverse]
QED

Theorem tpm_eql:
  tpm π t = u ⇔ t = tpm π⁻¹ u
Proof
  simp[tpm_eqr]
QED

(* NOTE: always use Once with it, to prevent infinite rewriting loops *)
Theorem tpm_CONS :
  tpm ((x,y)::pi) t = tpm [(x,y)] (tpm pi t)
Proof
  SRW_TAC [][GSYM pmact_decompose]
QED

Theorem tpm_SNOC :
    tpm (SNOC (x,y) pi) t = tpm pi (tpm [(x,y)] t)
Proof
    SIMP_TAC std_ss [SNOC_APPEND, GSYM pmact_decompose]
QED

val tpm_ALPHA = store_thm(
  "tpm_ALPHA",
  ``v ∉ FV u ==> (LAM x u = LAM v (tpm [(v,x)] u))``,
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, pmact_flip_args]);

(* cases theorem *)
val term_CASES = store_thm(
  "term_CASES",
  ``!t. (?s. t = VAR s) \/ (?t1 t2. t = t1 @@ t2) \/ (?v t0. t = LAM v t0)``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][] THEN METIS_TAC []);

(* should derive automatically *)
Theorem term_distinct[simp]:
  VAR s ≠ APP t1 t2 ∧ VAR s ≠ LAM v t ∧ APP t1 t2 ≠ LAM v t
Proof
  srw_tac [][VAR_def, APP_def, LAM_def, LAM_termP, VAR_termP, APP_termP,
             term_ABS_pseudo11, gterm_distinct, GLAM_eq_thm]
QED

Theorem term_11[simp]:
  (VAR s1 = VAR s2 <=> s1 = s2) ∧
  (t11 @@ t12 = t21 @@ t22 <=> t11 = t21 ∧ t12 = t22) ∧
  (LAM v t1 = LAM v t2 <=> t1 = t2)
Proof
  srw_tac [][VAR_def, APP_def, LAM_def, LAM_termP, VAR_termP, APP_termP,
             term_ABS_pseudo11, gterm_11, term_REP_11]
QED

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

(* ----------------------------------------------------------------------
    Establish substitution function
   ---------------------------------------------------------------------- *)

val tpm_COND = prove(
  ``tpm pi (if P then x else y) = if P then tpm pi x else tpm pi y``,
  SRW_TAC [][]);

val tpm_apart = store_thm(
  "tpm_apart",
  ``!t. ~(x IN FV t) /\ (y IN FV t) ==> ~(tpm [(x,y)] t = t)``,
  metis_tac[supp_apart, pmact_flip_args]);

val tpm_fresh = store_thm(
  "tpm_fresh",
  ``∀t x y. x ∉ FV t ∧ y ∉ FV t ==> (tpm [(x,y)] t = t)``,
  srw_tac [][supp_fresh]);

val rewrite_pairing = prove(
  ``(∃f: term -> (string # term) -> term. P f) <=>
    (∃f: term -> string -> term -> term. P (λM (x,N). f N x M))``,
  EQ_TAC >> strip_tac >| [
    qexists_tac `λN x M. f M (x,N)` >> srw_tac [][] >>
    CONV_TAC (DEPTH_CONV pairLib.PAIRED_ETA_CONV) >>
    srw_tac [ETA_ss][],
    qexists_tac `λM (x,N). f N x M` >> srw_tac [][]
  ]);

val subst_exists =
    parameter_tm_recursion
        |> INST_TYPE [alpha |-> ``:term``, ``:ρ`` |-> ``:string # term``]
        |> SPEC_ALL
        |> Q.INST [`A` |-> `{}`, `apm` |-> `^t_pmact_t`,
                   `ppm` |-> `pair_pmact string_pmact ^t_pmact_t`,
                   `vr` |-> `\s (x,N). if s = x then N else VAR s`,
                   `ap` |-> `\r1 r2 t1 t2 p. r1 p @@ r2 p`,
                   `lm` |-> `\r v t p. LAM v (r p)`]
        |> CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss()) [FORALL_PROD]))
        |> SIMP_RULE (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def,
                                 tpm_COND, tpm_fresh, pmact_sing_inv,
                                 basic_swapTheory.swapstr_eq_left]
        |> SIMP_RULE (srw_ss()) [rewrite_pairing, FORALL_PROD]
        |> CONV_RULE (DEPTH_CONV (rename_vars [("p_1", "u"), ("p_2", "N")]))
        |> prove_alpha_fcbhyp {ppm = ``pair_pmact string_pmact ^t_pmact_t``,
                               rwts = [],
                               alphas = [tpm_ALPHA]}

val SUB_DEF = new_specification("SUB_DEF", ["SUB"], subst_exists)

val _ = add_rule {term_name = "SUB", fixity = Closefix,
                  pp_elements = [TOK "[", TM, TOK "/", TM, TOK "]"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2))};

(* Give substitution theorems names compatible with historical usage *)

val SUB_THMv = prove(
  ``([N/x](VAR x) = N) /\ (~(x = y) ==> ([N/y](VAR x) = VAR x))``,
  SRW_TAC [][SUB_DEF]);
val SUB_COMM = prove(
  ``∀N x x' y t.
        x' ≠ x ∧ x' ∉ FV N ∧ y ≠ x ∧ y ∉ FV N ⇒
        (tpm [(x',y)] ([N/x] t) = [N/x] (tpm [(x',y)] t))``,
  srw_tac [][SUB_DEF, supp_fresh]);


val SUB_THM = save_thm(
  "SUB_THM",
  let val (eqns,_) = CONJ_PAIR SUB_DEF
  in
    CONJ (REWRITE_RULE [GSYM CONJ_ASSOC]
                       (LIST_CONJ (SUB_THMv :: tl (CONJUNCTS eqns))))
         SUB_COMM
  end)
val _ = export_rewrites ["SUB_THM"]
val SUB_VAR = save_thm("SUB_VAR", hd (CONJUNCTS SUB_DEF))

(* |- !v u N t. v <> u /\ v # N ==> [N/u] (LAM v t) = LAM v ([N/u] t) *)
Theorem SUB_LAM = List.nth (CONJUNCTS SUB_DEF, 2)

(* ----------------------------------------------------------------------
    Results about substitution
   ---------------------------------------------------------------------- *)

Theorem fresh_tpm_subst:
  !t. ~(u IN FV t) ==> (tpm [(u,v)] t = [VAR u/v] t)
Proof
  HO_MATCH_MP_TAC nc_INDUCTION THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]
QED

(* |- !t. u # t ==> tpm [(v,u)] t = [VAR u/v] t *)
Theorem fresh_tpm_subst' =
    ONCE_REWRITE_RULE [pmact_flip_args] fresh_tpm_subst

Theorem tpm_subst:
  !N. tpm pi ([M/v] N) = [tpm pi M/lswapstr pi v] (tpm pi N)
Proof
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  Q.EXISTS_TAC `v INSERT FV M` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem tpm_subst_out:
  [M/v] (tpm pi N) = tpm pi ([tpm (REVERSE pi) M/lswapstr (REVERSE pi) v] N)
Proof SRW_TAC [][tpm_subst]
QED

Theorem lemma14a[simp]:
  !t. [VAR v/v] t = t
Proof
  HO_MATCH_MP_TAC nc_INDUCTION THEN Q.EXISTS_TAC `{v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem lemma14b:
  !M. ~(v IN FV M) ==> ([N/v] M = M)
Proof
  HO_MATCH_MP_TAC nc_INDUCTION THEN Q.EXISTS_TAC `v INSERT FV N` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]
QED

(* Note: this is the opposite direction of lemma14b *)
Theorem SUB_FIX_IMP_NOTIN_FV :
    !x t. (!u. [u/x] t = t) ==> x NOTIN FV t
Proof
    rpt GEN_TAC
 >> Suff ‘(?u. u # t /\ [VAR u/x] t = t) ==> x # t’
 >- (rw [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q_TAC (NEW_TAC "z") ‘FV t’ \\
     Q.EXISTS_TAC ‘z’ >> rw [])
 >> simp [PULL_EXISTS]
 >> Q.X_GEN_TAC ‘u’
 >> Q.ID_SPEC_TAC ‘t’
 >> HO_MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘{x;u}’ >> rw []
 >> CCONTR_TAC >> fs []
QED

Theorem lemma14b_ext1 :
    !v M. v # M <=> !N. ([N/v] M = M)
Proof
    rpt GEN_TAC
 >> EQ_TAC >- rw [lemma14b]
 >> DISCH_TAC
 >> rw [SUB_FIX_IMP_NOTIN_FV]
QED

Theorem SUB_EQ_IMP_NOTIN_FV :
    !x t. (!t1 t2. [t1/x] t = [t2/x] t) ==> x NOTIN FV t
Proof
    rpt GEN_TAC
 >> Suff ‘(?u u'. u <> u' /\ u # t /\ u' # t /\
                  [VAR u/x] t = [VAR u'/x] t) ==> x # t’
 >- (rw [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q_TAC (NEW_TAC "z") ‘FV t’ \\
     Q.EXISTS_TAC ‘z’ >> rw [] \\
     Q_TAC (NEW_TAC "z'") ‘{z} UNION FV t’ \\
     Q.EXISTS_TAC ‘z'’ >> rw [])
 >> simp [PULL_EXISTS]
 >> rpt GEN_TAC
 >> Q.ID_SPEC_TAC ‘t’
 >> HO_MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘{x;u;u'}’ >> rw []
 >> CCONTR_TAC >> fs []
QED

Theorem lemma14b_ext2 :
    !v M. v # M <=> !N1 N2. [N1/v] M = [N2/v] M
Proof
    rpt GEN_TAC
 >> EQ_TAC >- rw [lemma14b]
 >> rw [SUB_EQ_IMP_NOTIN_FV]
QED

(* ‘tpm pi M’ doesn't change M if all its variables are irrelevant *)
Theorem tpm_unchanged :
    !pi M. DISJOINT (set (MAP FST pi)) (FV M) /\
           DISJOINT (set (MAP SND pi)) (FV M) ==> tpm pi M = M
Proof
    Induct_on ‘pi’
 >- rw []
 >> simp [pairTheory.FORALL_PROD]
 >> rw [Once tpm_CONS]
 >> Know ‘tpm [(p_1,p_2)] M = [VAR p_1/p_2] M’
 >- (MATCH_MP_TAC fresh_tpm_subst >> art [])
 >> Rewr'
 >> MATCH_MP_TAC lemma14b >> art []
QED

Theorem lemma14c:
  !t x u. x IN FV u ==> (FV ([t/x]u) = FV t UNION (FV u DELETE x))
Proof
  NTAC 2 GEN_TAC THEN HO_MATCH_MP_TAC nc_INDUCTION THEN
  Q.EXISTS_TAC `x INSERT FV t` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, EXTENSION] THEN
  METIS_TAC [lemma14b]
QED

Theorem FV_SUB:
  !t u v. FV ([t/v] u) = if v ∈ FV u then FV t ∪ (FV u DELETE v) else FV u
Proof PROVE_TAC [lemma14b, lemma14c]
QED

Theorem FV_SUB_SUBSET :
  !t u v. closed t ==> FV ([t/v] u) SUBSET FV u
Proof
    rw [FV_SUB, closed_def]
QED

Theorem FV_SUB_upperbound :
  !t u v. FV ([t/v] u) SUBSET FV u UNION FV t
Proof
    rw [FV_SUB]
 >> ASM_SET_TAC []
QED

Theorem lemma15a:
  !M. v ∉ FV M ==> [N/v]([VAR v/x]M) = [N/x]M
Proof
  HO_MATCH_MP_TAC nc_INDUCTION THEN Q.EXISTS_TAC `{x;v} UNION FV N` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem lemma15b:
  v ∉ FV M ==> [VAR u/v]([VAR v/u] M) = M
Proof SRW_TAC [][lemma15a]
QED

Theorem SUB_TWICE_ONE_VAR :
    !body. [x/v] ([y/v] body) = [[x/v]y / v] body
Proof
  HO_MATCH_MP_TAC nc_INDUCTION THEN SRW_TAC [][SUB_THM, SUB_VAR] THEN
  Q.EXISTS_TAC `v INSERT FV x UNION FV y` THEN
  SRW_TAC [][SUB_THM] THEN
  Cases_on `v IN FV y` THEN SRW_TAC [][SUB_THM, lemma14c, lemma14b]
QED

Theorem swap_eq_3substs:
  z ∉ FV M ∧ x ≠ z ∧ y ≠ z ⇒
  tpm [(x, y)] M = [VAR y/z] ([VAR x/y] ([VAR z/x] M))
Proof
  SRW_TAC [][GSYM fresh_tpm_subst] THEN
  ‘tpm [(x,y)] (tpm [(z,x)] M) =
       tpm [(swapstr x y z, swapstr x y x)] (tpm [(x,y)] M)’
     by (SRW_TAC [][Once (GSYM pmact_sing_to_back), SimpLHS] THEN
         SRW_TAC [][]) THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  SRW_TAC [][pmact_flip_args]
QED

(* ----------------------------------------------------------------------
    alpha-convertibility results
   ---------------------------------------------------------------------- *)

Theorem SIMPLE_ALPHA:
  y ∉ FV u ==> !x. LAM x u = LAM y ([VAR y/x] u)
Proof
  SRW_TAC [][GSYM fresh_tpm_subst] THEN
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, pmact_flip_args]
QED

(* ----------------------------------------------------------------------
    size function
   ---------------------------------------------------------------------- *)

val size_exists =
    tm_recursion
        |> INST_TYPE [alpha |-> ``:num``]
        |> SPEC_ALL
        |> Q.INST [`A` |-> `{}`, `apm` |-> `discrete_pmact`,
             `vr` |-> `\s. 1`, `ap` |-> `\m n t1 t2. m + n + 1`,
             `lm` |-> `\m v t. m + 1`]
        |> SIMP_RULE (srw_ss()) []

val size_def = new_specification("size_def", ["size"], size_exists)
Theorem size_thm[simp] = CONJUNCT1 size_def

Theorem size_tpm[simp] = GSYM (CONJUNCT2 size_def)

Theorem size_nonzero :
    !t:term. 0 < size t
Proof
    HO_MATCH_MP_TAC simple_induction
 >> SRW_TAC [ARITH_ss][]
QED

(* |- !t. size t <> 0 *)
Theorem size_nz =
    REWRITE_RULE [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO] size_nonzero

Theorem size_1_cases :
    (size M = 1) <=> ?y. (M = VAR y)
Proof
    Q.SPEC_THEN `M` STRUCT_CASES_TAC term_CASES
 >> SRW_TAC [][size_thm, size_nz]
QED

(* moved here from standardisationScript.sml *)
Theorem size_vsubst[simp]:
    !M:term. size ([VAR v/u] M) = size M
Proof
  HO_MATCH_MP_TAC nc_INDUCTION THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_VAR, SUB_THM]
QED

Theorem size_foldl_app :
    !args t : term.
       size (FOLDL APP t args) = FOLDL (\n t. n + size t + 1) (size t) args
Proof
  Induct THEN SRW_TAC [][size_thm]
QED

Theorem size_foldl_app_lt :
    !(args : term list) x. x <= FOLDL (\n t. n + size t + 1) x args
Proof
  Induct THEN SRW_TAC [][] THEN
  `x + size h + 1 <= FOLDL (\n t. n + size t + 1) (x + size h + 1) args`
     by METIS_TAC [] THEN
  DECIDE_TAC
QED

Theorem size_args_foldl_app :
    !args n (t : term) x. n < LENGTH args ==>
                size (EL n args) < x + size (FOLDL APP t args)
Proof
  Induct THEN SRW_TAC [][] THEN
  Cases_on `n` THEN SRW_TAC [][] THENL [
    SRW_TAC [][size_foldl_app, size_thm] THEN
    `size t + size h + 1 <=
       FOLDL (\n t. n + size t + 1) (size t + size h + 1) args`
       by SRW_TAC [][size_foldl_app_lt] THEN
    DECIDE_TAC,
    FULL_SIMP_TAC (srw_ss()) []
  ]
QED

(* ----------------------------------------------------------------------
    iterated substitutions (ugh)
   ---------------------------------------------------------------------- *)

Definition ISUB_def:
     ($ISUB t [] = t)
  /\ ($ISUB t ((s,x)::rst) = $ISUB ([s/x]t) rst)
End
val _ = export_rewrites ["ISUB_def"];

val _ = set_fixity "ISUB" (Infixr 501);

Definition DOM_DEF :
   (DOM [] = {}) /\
   (DOM ((x,y)::rst) = {y} UNION DOM rst)
End

Theorem DOM_SNOC :
    !x y rst. DOM (SNOC (x,y) rst) = {y} UNION DOM rst
Proof
    NTAC 2 GEN_TAC
 >> Induct_on ‘rst’ >- rw [DOM_DEF]
 >> simp [FORALL_PROD]
 >> rw [DOM_DEF]
 >> SET_TAC []
QED

Theorem DOM_ALT_MAP_SND :
    !phi. DOM phi = set (MAP SND phi)
Proof
    Induct_on ‘phi’ >- rw [DOM_DEF]
 >> Q.X_GEN_TAC ‘h’
 >> Cases_on ‘h’
 >> rw [DOM_DEF] >> SET_TAC []
QED

Definition FVS_DEF :
   (FVS [] = {}) /\
   (FVS ((t,x)::rst) = FV t UNION FVS rst)
End

Theorem FVS_SNOC :
    !t x rst. FVS (SNOC (t,x) rst) = FV t UNION FVS rst
Proof
    NTAC 2 GEN_TAC
 >> Induct_on ‘rst’ >- rw [FVS_DEF]
 >> simp [FORALL_PROD]
 >> rw [FVS_DEF]
 >> SET_TAC []
QED

Theorem FVS_ALT :
    !ss. FVS ss = BIGUNION (set (MAP (FV o FST) ss))
Proof
    Induct_on ‘ss’
 >> simp [FORALL_PROD, FVS_DEF]
QED

Theorem FINITE_DOM[simp] :
    !ss. FINITE (DOM ss)
Proof
    Induct >| [ALL_TAC, Cases]
 >> RW_TAC std_ss [DOM_DEF, FINITE_EMPTY, FINITE_UNION, FINITE_SING]
QED

Theorem FINITE_FVS[simp] :
    !ss. FINITE (FVS ss)
Proof
    Induct >| [ALL_TAC, Cases]
 >> RW_TAC std_ss [FVS_DEF, FINITE_EMPTY, FINITE_UNION, FINITE_FV]
QED

Theorem ISUB_LAM[simp] :
    !R x. x NOTIN DOM R /\ x NOTIN FVS R ==>
          !t. (LAM x t) ISUB R = LAM x (t ISUB R)
Proof
    Induct
 >> ASM_SIMP_TAC (srw_ss()) [ISUB_def, FORALL_PROD,
                             DOM_DEF, FVS_DEF, SUB_THM]
QED

Theorem SUB_ISUB_SINGLETON :
    !t x u. [t/x]u:term = u ISUB [(t,x)]
Proof
    SRW_TAC [][ISUB_def]
QED

Theorem ISUB_APPEND :
    !R1 R2 t:term. (t ISUB R1) ISUB R2 = t ISUB (APPEND R1 R2)
Proof
    Induct
 >> ASM_SIMP_TAC (srw_ss()) [FORALL_PROD, ISUB_def]
QED

(* moved here from standardisationScript.sml *)
Theorem ISUB_APP :
    !sub M N. (M @@ N) ISUB sub = (M ISUB sub) @@ (N ISUB sub)
Proof
    Induct
 >> ASM_SIMP_TAC (srw_ss()) [FORALL_PROD, ISUB_def, SUB_THM]
QED

(* NOTE: This is actually appFOLDLTheory.appstar_ISUB *)
Theorem FOLDL_APP_ISUB :
    !args (t:term) sub.
         FOLDL APP t args ISUB sub =
         FOLDL APP (t ISUB sub) (MAP (\t. t ISUB sub) args)
Proof
    Induct >> SRW_TAC [][ISUB_APP]
QED

(* NOTE: This is the basis of a "lemma14b" for ISUB, cf. ssub_14b *)
Theorem ISUB_VAR_FRESH :
    !y sub. ~MEM y (MAP SND sub) ==> (VAR y ISUB sub = VAR y)
Proof
    Q.X_GEN_TAC ‘x’
 >> Induct_on ‘sub’ >> rw [ISUB_def]
 >> Cases_on ‘h’ >> fs []
 >> rw [ISUB_def, SUB_VAR]
QED

(* |- !y sub. y NOTIN DOM sub ==> VAR y ISUB sub = VAR y *)
Theorem ISUB_VAR_FRESH' = REWRITE_RULE [GSYM DOM_ALT_MAP_SND] ISUB_VAR_FRESH

Theorem ISUB_unchanged :
    !ss t. DISJOINT (FV t) (DOM ss) ==> t ISUB ss = t
Proof
    Induct_on ‘ss’
 >- rw [DOM_DEF]
 >> simp [FORALL_PROD] >> qx_genl_tac [‘N’, ‘v’]
 >> rw [DOM_DEF]
 >> simp [lemma14b]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> rw [Once DISJOINT_SYM]
QED

Theorem tpm1_ISUB_exists[local] :
    !M x y. ?ss. tpm [(x,y)] M = M ISUB ss
Proof
    rpt GEN_TAC
 >> Cases_on ‘x # M’
 >- (rw [fresh_tpm_subst] \\
     Q.EXISTS_TAC ‘[(VAR x,y)]’ >> rw [])
 >> Cases_on ‘y # M’
 >- (rw [Once pmact_flip_args, fresh_tpm_subst] \\
     Q.EXISTS_TAC ‘[(VAR y,x)]’ >> rw [])
 (* stage work *)
 >> fs []
 >> Q_TAC (NEW_TAC "z") ‘FV M UNION {x} UNION {y}’
 (* applying swap_eq_3substs *)
 >> Q.EXISTS_TAC ‘[(VAR z,x);(VAR x,y);(VAR y,z)]’
 >> rw [swap_eq_3substs]
QED

Theorem tpm_ISUB_exists :
    !pi M. ?ss. tpm pi M = M ISUB ss
Proof
    Induct_on ‘pi’
 >- (rw [] >> Q.EXISTS_TAC ‘[]’ >> rw [])
 >> rpt GEN_TAC
 >> Cases_on ‘h’
 >> rw [Once tpm_CONS]
 >> STRIP_ASSUME_TAC (Q.SPECL [‘tpm pi M’, ‘q’, ‘r’] tpm1_ISUB_exists)
 >> POP_ORW
 >> POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC ‘M’))
 >> POP_ORW
 >> rw [ISUB_APPEND]
 >> Q.EXISTS_TAC ‘ss' ++ ss’ >> rw []
QED

Theorem FV_ISUB_SUBSET :
    !sub u. FVS sub = {} ==> FV (u ISUB sub) SUBSET FV u
Proof
    Induct_on ‘sub’ >- rw []
 >> SIMP_TAC std_ss [FORALL_PROD]
 >> rw [FVS_DEF, ISUB_def]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘FV ([p_1/p_2] u)’
 >> CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> MATCH_MP_TAC FV_SUB_SUBSET
 >> rw [closed_def]
QED

Theorem FV_ISUB_upperbound :
    !sub u. FV (u ISUB sub) SUBSET FV u UNION FVS sub
Proof
    Induct_on ‘sub’ >- rw []
 >> SIMP_TAC std_ss [FORALL_PROD]
 >> rw [FVS_DEF, ISUB_def]
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV ([p_1/p_2] u) UNION FVS sub’
 >> simp []
 >> reverse CONJ_TAC >- SET_TAC []
 (* applying FV_SUB_upperbound *)
 >> Q_TAC (TRANS_TAC SUBSET_TRANS) ‘FV u UNION FV p_1’
 >> simp [FV_SUB_upperbound]
 >> SET_TAC []
QED

(* This is a direct generalization of fresh_tpm_subst

   NOTE: cf. fresh_tpm_isub' for another version without REVERSE.
 *)
Theorem fresh_tpm_isub :
    !xs ys t. LENGTH xs = LENGTH ys /\ ALL_DISTINCT ys /\
              DISJOINT (set ys) (FV t)
          ==> tpm (ZIP (xs,ys)) t =
              t ISUB (ZIP (MAP VAR (REVERSE ys), REVERSE xs))
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘pi = ZIP (xs,ys)’
 >> ‘xs = MAP FST pi /\ ys = MAP SND pi’ by simp [Abbr ‘pi’, MAP_ZIP]
 >> Q.PAT_X_ASSUM ‘DISJOINT (set ys) (FV t)’ MP_TAC
 >> Q.PAT_X_ASSUM ‘ALL_DISTINCT ys’ MP_TAC
 >> NTAC 2 POP_ORW
 >> KILL_TAC
 >> Q.ID_SPEC_TAC ‘t’
 >> Induct_on ‘pi’ >- simp []
 >> simp [FORALL_PROD]
 >> qx_gen_tac ‘u’
 >> qx_gen_tac ‘v’
 >> rw [Once tpm_CONS]
 >> qabbrev_tac ‘xs = MAP FST pi’
 >> qabbrev_tac ‘ys = MAP SND pi’
 >> ‘LENGTH xs = LENGTH ys’ by rw [Abbr ‘xs’, Abbr ‘ys’]
 >> qabbrev_tac ‘ss = ZIP (MAP VAR (REVERSE ys),REVERSE xs)’
 >> Know ‘ZIP (MAP VAR (REVERSE ys) ++ [VAR v],REVERSE xs ++ [u]) =
          ss ++ [(VAR v,u)]’
 >- simp [GSYM ZIP_APPEND]
 >> Rewr'
 >> simp [GSYM ISUB_APPEND]
 >> MATCH_MP_TAC fresh_tpm_subst'
 >> Suff ‘v NOTIN (FV t UNION FVS ss)’
 >- METIS_TAC [FV_ISUB_upperbound, SUBSET_DEF]
 >> Know ‘FVS ss = set ys’
 >- (simp [FVS_ALT, Abbr ‘ss’, MAP_ZIP, MAP_MAP_o] \\
     rw [Once EXTENSION] >> EQ_TAC >> rw [MEM_MAP] >- fs [] \\
     Q.EXISTS_TAC ‘{x}’ >> simp [])
 >> Rewr'
 >> CCONTR_TAC >> gs []
QED

Theorem ISUB_SNOC :
    !s x rst t. t ISUB SNOC (s,x) rst = [s/x] (t ISUB rst)
Proof
    NTAC 2 GEN_TAC
 >> Induct_on ‘rst’ >- rw []
 >> simp [FORALL_PROD]
QED

(* ----------------------------------------------------------------------
    RENAMING: a special iterated substitutions like tpm
   ---------------------------------------------------------------------- *)

(* moved here from standardisationScript.sml *)
Definition RENAMING_def :
  (RENAMING []     <=> T) /\
  (RENAMING (h::t) <=> (?y x:string. (h = (VAR y:term,x))) /\ RENAMING t)
End

val _ = export_rewrites ["RENAMING_def"]

Theorem RENAMING_APPEND :
    !l1 l2. RENAMING (APPEND l1 l2) <=> RENAMING l1 /\ RENAMING l2
Proof
    Induct >> SRW_TAC [][] >> METIS_TAC []
QED

(* |- ((RENAMING [] <=> T) /\
       !h t. RENAMING (h::t) <=> (?y x. h = (VAR y,x)) /\ RENAMING t) /\
      !l1 l2. RENAMING (l1 ++ l2) <=> RENAMING l1 /\ RENAMING l2
 *)
Theorem RENAMING_THM = CONJ RENAMING_def RENAMING_APPEND

Theorem RENAMING_REVERSE[simp] :
    !R. RENAMING (REVERSE R) = RENAMING R
Proof
    Induct >> SRW_TAC [][RENAMING_APPEND, RENAMING_THM] >> METIS_TAC []
QED

Theorem RENAMING_ZIP :
    !l1 l2. (LENGTH l1 = LENGTH l2) ==>
            (RENAMING (ZIP (l1, l2)) = !e. MEM e l1 ==> ?s. e = VAR s)
Proof
    Induct >> Cases_on `l2`
 >> SRW_TAC [][RENAMING_THM] >> PROVE_TAC []
QED

Theorem RENAMING_ZIP_MAP_VAR[simp] :
    !l1 l2. (LENGTH l1 = LENGTH l2) ==> RENAMING (ZIP (MAP VAR l1, l2))
Proof
    Induct >> Cases_on `l2`
 >> SRW_TAC [][RENAMING_ZIP, listTheory.MEM_MAP]
 >> SRW_TAC [][]
QED

Theorem size_ISUB :
    !R N:term. RENAMING R ==> (size (N ISUB R) = size N)
Proof
  Induct THEN
  ASM_SIMP_TAC (srw_ss())[ISUB_def, FORALL_PROD,
                          RENAMING_THM] THEN
  SRW_TAC [][] THEN SRW_TAC [][size_vsubst]
QED

(* ----------------------------------------------------------------------
    Simultaneous substitution (using a finite map) - much more interesting
   ---------------------------------------------------------------------- *)

Overload fmFV = “supp (fm_pmact string_pmact ^t_pmact_t)”
Overload tmsFV = “supp (set_pmact ^t_pmact_t)”
Overload fmtpm = “fmpm string_pmact term_pmact”

Theorem strterm_fmap_supp:
  fmFV fmap = FDOM fmap ∪ tmsFV (FRANGE fmap)
Proof SRW_TAC [][fmap_supp]
QED

Theorem FINITE_strterm_fmap_supp[simp]:
  FINITE (fmFV fmap)
Proof
  SRW_TAC [][strterm_fmap_supp, supp_setpm] THEN SRW_TAC [][]
QED

val lem1 = prove(
  ``∃a. ~(a ∈ supp (fm_pmact string_pmact ^t_pmact_t) fm)``,
  Q_TAC (NEW_TAC "z") `supp (fm_pmact string_pmact ^t_pmact_t) fm` THEN
  METIS_TAC []);

val supp_FRANGE = prove(
  ``~(x ∈ supp (set_pmact ^t_pmact_t) (FRANGE fm)) =
   ∀y. y ∈ FDOM fm ==> ~(x ∈ FV (fm ' y))``,
  SRW_TAC [][supp_setpm, finite_mapTheory.FRANGE_DEF] THEN METIS_TAC []);

fun ex_conj1 thm = let
  val (v,c) = dest_exists (concl thm)
  val c1 = CONJUNCT1 (ASSUME c)
  val fm = mk_exists(v,concl c1)
in
  CHOOSE (v, thm) (EXISTS(fm,v) c1)
end

val supp_EMPTY = prove(
  ``(supp (set_pmact apm) {} = {})``,
  srw_tac [][EXTENSION] >> match_mp_tac notinsupp_I >>
  qexists_tac `{}` >> srw_tac [][support_def]);


Theorem lem2[local]: ∀fm. FINITE (tmsFV (FRANGE fm))
Proof
  srw_tac [][supp_setpm] >> srw_tac [][]
QED

val ordering = prove(
  ``(∃f. P f) <=> (∃f. P (combin$C f))``,
  srw_tac [][EQ_IMP_THM] >-
    (qexists_tac `λx y. f y x` >> srw_tac [ETA_ss][combinTheory.C_DEF]) >>
  metis_tac [])

Theorem notin_frange:
  v ∉ tmsFV (FRANGE p) <=> ∀y. y ∈ FDOM p ==> v ∉ FV (p ' y)
Proof
  srw_tac [][supp_setpm, EQ_IMP_THM, finite_mapTheory.FRANGE_DEF] >>
  metis_tac []
QED

(*****************************************************************************)
(*   Simultaneous substitution based on finite maps (ssub)                   *)
(*****************************************************************************)

val ssub_exists =
    parameter_tm_recursion
        |> INST_TYPE [alpha |-> ``:term``, ``:ρ`` |-> ``:string |-> term``]
        |> Q.INST [`vr` |-> `\s fm. if s ∈ FDOM fm then fm ' s else VAR s`,
                   `lm` |-> `\r v t fm. LAM v (r fm)`, `apm` |-> `^t_pmact_t`,
                   `ppm` |-> `fm_pmact string_pmact ^t_pmact_t`,
                   `ap` |-> `\r1 r2 t1 t2 fm. r1 fm @@ r2 fm`,
                   `A` |-> `{}`]
        |> SIMP_RULE (srw_ss()) [tpm_COND, strterm_fmap_supp, lem2,
                                 FAPPLY_eqv_lswapstr, supp_fresh,
                                 pmact_sing_inv, fnpm_def,
                                 fmpm_FDOM, notin_frange]
        |> SIMP_RULE (srw_ss()) [Once ordering]
        |> CONV_RULE (DEPTH_CONV (rename_vars [("p", "fm")]))
        |> prove_alpha_fcbhyp {ppm = ``fm_pmact string_pmact ^t_pmact_t``,
                               rwts = [notin_frange, strterm_fmap_supp],
                               alphas = [tpm_ALPHA]}

val ssub_def = new_specification ("ssub_def", ["ssub"], ssub_exists)

(* |- (!s fm. fm ' (VAR s) = if s IN FDOM fm then fm ' s else VAR s) /\
      (!fm t t'. fm ' (t' @@ t) = fm ' t' @@ fm ' t) /\
      !v fm t.
        v NOTIN FDOM fm /\ (!y. y IN FDOM fm ==> v # fm ' y) ==>
        (fm ' (LAM v t) = LAM v (fm ' t))
 *)
Theorem ssub_thm[simp] = CONJUNCT1 ssub_def

val _ = overload_on ("'", ``ssub``)

val tpm_ssub = save_thm("tpm_ssub", CONJUNCT2 ssub_def)

val single_ssub = store_thm(
  "single_ssub",
  ``∀N. (FEMPTY |+ (s,M)) ' N = [M/s]N``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN Q.EXISTS_TAC `s INSERT FV M` THEN
  SRW_TAC [][SUB_VAR, SUB_THM]);

Theorem in_fmap_supp:
  x ∈ fmFV fm ⇔ x ∈ FDOM fm ∨ ∃y. y ∈ FDOM fm ∧ x ∈ FV (fm ' y)
Proof
  SRW_TAC [][strterm_fmap_supp, nomsetTheory.supp_setpm] THEN
  SRW_TAC [boolSimps.DNF_ss][finite_mapTheory.FRANGE_DEF] THEN METIS_TAC []
QED

Theorem not_in_fmap_supp[simp]:
  x ∉ fmFV fm <=> x ∉ FDOM fm ∧ ∀y. y ∈ FDOM fm ==> x ∉ FV (fm ' y)
Proof
  METIS_TAC [in_fmap_supp]
QED

Theorem ssub_14a :
    !t. (!x. x IN FDOM fm ==> fm ' x = VAR x) ==>
        (fm : string |-> term) ' t = t
Proof
    HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘fmFV fm’
 >> rw []
QED

Theorem ssub_14b:
  ∀t. (FV t ∩ FDOM phi = EMPTY) ==> ((phi : string |-> term) ' t = t)
Proof
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  Q.EXISTS_TAC `fmFV phi` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, pred_setTheory.EXTENSION] THEN METIS_TAC []
QED

(* |- !t. DISJOINT (FV t) (FDOM phi) ==> phi ' t = t *)
Theorem ssub_14b' = ssub_14b |> REWRITE_RULE [GSYM DISJOINT_DEF]

val ssub_value = store_thm(
  "ssub_value",
  ``(FV t = EMPTY) ==> ((phi : string |-> term) ' t = t)``,
  SRW_TAC [][ssub_14b]);

Theorem ssub_FEMPTY[simp]:
  ∀t. (FEMPTY:string|->term) ' t = t
Proof
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]
QED

Theorem FV_ssub :
    !fm N. (!y. y IN FDOM fm ==> FV (fm ' y) = {}) ==>
           FV (fm ' N) = FV N DIFF FDOM fm
Proof
    rpt STRIP_TAC
 >> Q.ID_SPEC_TAC ‘N’
 >> HO_MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘FDOM fm’
 >> rw [SUB_VAR, SUB_THM, ssub_thm]
 >> SET_TAC []
QED

Theorem fresh_ssub:
  ∀N. y ∉ FV N ∧ (∀k:string. k ∈ FDOM fm ⇒ y # fm ' k) ⇒ y # fm ' N
Proof
  ho_match_mp_tac nc_INDUCTION >>
  qexists ‘fmFV fm’ >>
  rw[] >> metis_tac[]
QED

Theorem ssub_SUBST:
  ∀M.
    (∀k. k ∈ FDOM fm ⇒ v # fm ' k) ∧ v ∉ FDOM fm ⇒
    fm ' ([N/v]M) = [fm ' N / v] (fm ' M)
Proof
  ho_match_mp_tac nc_INDUCTION >>
  qexists ‘fmFV fm ∪ {v} ∪ FV N’ >>
  rw[] >> rw[lemma14b, SUB_VAR] >>
  gvs[DECIDE “~p ∨ q ⇔ p ⇒ q”, PULL_FORALL] >>
  rename1 ‘y # N’ >>
  ‘y # fm ' N’ suffices_by simp[SUB_THM] >>
  irule fresh_ssub >> simp[]
QED

(* |- !v fm t.
        v NOTIN FDOM fm /\ (!y. y IN FDOM fm ==> v # fm ' y) ==>
        fm ' (LAM v t) = LAM v (fm ' t)
 *)
Theorem ssub_LAM = List.nth(CONJUNCTS ssub_thm, 2)

Theorem ssub_update_apply :
    !fm v N M. v NOTIN FDOM fm /\ (!k. k IN FDOM fm ==> closed (fm ' k)) ==>
              (fm |+ (v,N)) ' M = [N/v] (fm ' (M :term))
Proof
    RW_TAC std_ss [closed_def]
 >> Q.ID_SPEC_TAC ‘M’
 >> HO_MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘v INSERT (FDOM fm UNION FV N)’
 >> rw [SUB_VAR, SUB_THM, ssub_thm, FAPPLY_FUPDATE_THM]
 >> TRY (METIS_TAC [])
 >- (MATCH_MP_TAC (GSYM lemma14b) \\
     METIS_TAC [NOT_IN_EMPTY])
 >> rename1 ‘y # N’
 >> Suff ‘(fm |+ (v,N)) ' (LAM y M) = LAM y ((fm |+ (v,N)) ' M)’ >- rw []
 >> MATCH_MP_TAC ssub_LAM
 >> rw [FAPPLY_FUPDATE_THM]
QED

(* NOTE: This theorem has the same antecedents as ssub_SUBST, plus:

   ‘DISJOINT (FV N) (FDOM fm)’, which seems necessary.
 *)
Theorem ssub_update_apply_SUBST :
    !M. (!k. k IN FDOM fm ==> v # fm ' k) /\ v NOTIN FDOM fm /\
        DISJOINT (FDOM fm) (FV N) ==>
        (fm |+ (v,N)) ' M = fm ' ([N/v] M)
Proof
    HO_MATCH_MP_TAC nc_INDUCTION
 >> Q.EXISTS_TAC ‘v INSERT fmFV fm UNION FV M UNION FV N’
 >> rw [SUB_VAR, SUB_THM, ssub_thm, FAPPLY_FUPDATE_THM]
 >> TRY (METIS_TAC [])
 >- (MATCH_MP_TAC (GSYM ssub_14b) \\
     rw [GSYM DISJOINT_DEF, Once DISJOINT_SYM])
 >> rename1 ‘y # N’
 >> Know ‘(fm |+ (v,N)) ' (LAM y M') = LAM y ((fm |+ (v,N)) ' M')’
 >- (MATCH_MP_TAC ssub_LAM >> rw [FAPPLY_FUPDATE_THM])
 >> Rewr'
 (* finally, applying IH *)
 >> rw []
QED

(* A combined version of ssub_update_apply_SUBST and ssub_SUBST *)
Theorem ssub_update_apply_SUBST' :
    !M fm v N.
       (!k. k IN FDOM fm ==> v # fm ' k) /\ v NOTIN FDOM fm /\
        DISJOINT (FDOM fm) (FV N) ==>
        (fm |+ (v,N)) ' M = [fm ' N/v] (fm ' M)
Proof
    rpt STRIP_TAC
 >> Know ‘[fm ' N/v] (fm ' M) = fm ' ([N/v] M)’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ]  \\
     MATCH_MP_TAC ssub_SUBST >> art [])
 >> Rewr'
 >> MATCH_MP_TAC ssub_update_apply_SUBST >> art []
QED

Theorem FEMPTY_update_apply :
    !M. (FEMPTY |+ (v,N)) ' M = [N/v] M
Proof
    Q.X_GEN_TAC ‘M’
 >> ‘[N/v] M = FEMPTY ' ([N/v] M)’ by rw []
 >> POP_ORW
 >> MATCH_MP_TAC ssub_update_apply_SUBST
 >> rw []
QED

Theorem ssub_update_apply_subst :
    !fm v N M. v NOTIN FDOM fm /\
              (!k. k IN FDOM fm ==> closed (fm ' k)) /\ closed N ==>
              (fm |+ (v,N)) ' M = fm ' ([N/v] M)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ssub_update_apply_SUBST >> art []
 >> fs [closed_def, DISJOINT_DEF]
QED

Theorem ssub_reduce_thm :
    !t. FV t INTER FDOM fm = {s} ==> fm ' t = [fm ' s/s] t
Proof
    HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘fmFV fm UNION {s}’
 >> rw [SUB_THM, ssub_thm]
 >- (‘s' = s’ by ASM_SET_TAC [] >> fs [])
 >- (‘s' = s’ by ASM_SET_TAC [] >> fs [ssub_thm] \\
     ‘s IN FDOM fm’ by ASM_SET_TAC [])
 >- (‘FV t INTER FDOM fm = {s} \/ FV t INTER FDOM fm = {}’ by ASM_SET_TAC []
     >- rw [] \\
     rw [ssub_14b] \\
     MATCH_MP_TAC (GSYM lemma14b) \\
     ASM_SET_TAC [])
 >- (‘FV t' INTER FDOM fm = {s} \/ FV t' INTER FDOM fm = {}’ by ASM_SET_TAC []
     >- rw [] \\
     rw [ssub_14b] \\
     MATCH_MP_TAC (GSYM lemma14b) \\
     ASM_SET_TAC [])
 >> ‘s IN FDOM fm’ by ASM_SET_TAC []
 >> Know ‘[fm ' s/s] (LAM y t) = LAM y ([fm ' s/s] t)’
 >- (MATCH_MP_TAC SUB_LAM >> rw [])
 >> Rewr'
 >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> ASM_SET_TAC []
QED

Theorem ssub_reduce :
    !t. FV t = {s} /\ s IN FDOM fm ==> fm ' t = [fm ' s/s] t
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ssub_reduce_thm
 >> ASM_SET_TAC []
QED

(* ----------------------------------------------------------------------
    Simultaneous substitution given by a pair of key list and value list
   ---------------------------------------------------------------------- *)

(* from a key list and a value list (of same length) to an alist *)
Definition fromPairs_def :
    fromPairs (Xs :string list) (Ps :term list) = FEMPTY |++ ZIP (Xs,Ps)
End

Theorem fromPairs_single :
    !X E E'. ssub (fromPairs [X] [E']) E = [E'/X] E
Proof
    RW_TAC list_ss [fromPairs_def, ZIP, FUPDATE_LIST_THM]
 >> rw [FEMPTY_update_apply]
QED

Theorem fromPairs_EMPTY :
    fromPairs [] [] = FEMPTY
Proof
    SRW_TAC [] [fromPairs_def, FUPDATE_LIST_THM]
QED

Theorem fromPairs_HD :
    !X Xs P Ps. ~MEM X Xs /\ LENGTH Ps = LENGTH Xs ==>
                fromPairs (X::Xs) (P::Ps) = fromPairs Xs Ps |+ (X,P)
Proof
    SRW_TAC [] [fromPairs_def, FUPDATE_LIST_THM]
 >> MATCH_MP_TAC FUPDATE_FUPDATE_LIST_COMMUTES
 >> METIS_TAC [MAP_ZIP]
QED

Theorem FDOM_fromPairs :
    !Xs Ps. LENGTH Ps = LENGTH Xs ==> FDOM (fromPairs Xs Ps) = set Xs
Proof
    SRW_TAC [] [fromPairs_def, FDOM_FUPDATE_LIST, MAP_ZIP]
QED

Theorem fromPairs_DOMSUB_NOT_IN_DOM :
    !X Xs Ps. ~MEM X Xs /\ LENGTH Ps = LENGTH Xs ==>
              fromPairs Xs Ps \\ X = fromPairs Xs Ps
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC DOMSUB_NOT_IN_DOM
 >> fs [FDOM_fromPairs]
QED

Theorem fromPairs_FAPPLY_HD :
    !X Xs P Ps n. ~MEM X Xs /\ ALL_DISTINCT Xs /\ (LENGTH Ps = LENGTH Xs) ==>
                  fromPairs (X::Xs) (P::Ps) ' X = P
Proof
    RW_TAC std_ss [fromPairs_HD, FAPPLY_FUPDATE]
QED

Theorem fromPairs_FAPPLY_EL :
    !Xs Ps n. ALL_DISTINCT Xs /\ LENGTH Ps = LENGTH Xs /\ n < LENGTH Xs ==>
              fromPairs Xs Ps ' (EL n Xs) = EL n Ps
Proof
    RW_TAC std_ss [fromPairs_def]
 >> MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM
 >> Q.EXISTS_TAC `n`
 >> fs [LENGTH_ZIP, MAP_ZIP]
 >> RW_TAC list_ss []
 >> CCONTR_TAC >> fs []
 >> `n < LENGTH Xs /\ m <> n` by RW_TAC arith_ss []
 >> METIS_TAC [ALL_DISTINCT_EL_IMP]
QED

Theorem fromPairs_FAPPLY_EL' :
    !X P Xs Ps n. ~MEM X Xs /\ ALL_DISTINCT Xs /\ LENGTH Ps = LENGTH Xs /\
                  n < LENGTH Xs
              ==> fromPairs (X::Xs) (P::Ps) ' (EL n Xs) = EL n Ps
Proof
    RW_TAC std_ss [fromPairs_HD, fromPairs_def]
 >> Know `((FEMPTY |++ ZIP (Xs,Ps)) |+ (X,P)) = ((FEMPTY |+ (X,P)) |++ ZIP (Xs,Ps))`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC FUPDATE_FUPDATE_LIST_COMMUTES \\
     fs [MAP_ZIP])
 >> Rewr'
 >> MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM
 >> Q.EXISTS_TAC `n`
 >> fs [LENGTH_ZIP, MAP_ZIP]
 >> RW_TAC list_ss []
 >> CCONTR_TAC >> fs []
 >> `n < LENGTH Xs /\ m <> n` by RW_TAC arith_ss []
 >> METIS_TAC [ALL_DISTINCT_EL_IMP]
QED

Theorem fromPairs_elim :
    !Xs Ps E. DISJOINT (FV E) (set Xs) /\ LENGTH Ps = LENGTH Xs ==>
              fromPairs Xs Ps ' E = E
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ssub_14b
 >> fs [FDOM_fromPairs, DISJOINT_DEF]
QED

Theorem lemma0[local] :
    !X P E fm. X NOTIN FDOM fm /\ DISJOINT (FDOM fm) (FV P) /\
               FEVERY (\(k,v). X NOTIN (FV v)) fm ==>
              (fm |+ (X,P)) ' E = [P/X] (fm ' E)
Proof
    rw []
 (* applying ssub_update_apply_subst *)
 >> Know ‘ssub (fm |+ (X,P)) E = [ssub fm P/X] (ssub fm E)’
 >- (MATCH_MP_TAC ssub_update_apply_SUBST' >> fs [FEVERY_DEF])
 >> Rewr'
 >> Suff ‘ssub fm P = P’ >- rw []
 >> MATCH_MP_TAC ssub_14b
 >> rw [GSYM DISJOINT_DEF, DISJOINT_SYM]
QED

(* fromPairs_reduce leads to fromPairs_FOLDR

   NOTE: added ‘DISJOINT (set Xs) (FV P)’ when switching to ‘ssub’
 *)
Theorem fromPairs_reduce :
    !X Xs P Ps. ~MEM X Xs /\ ALL_DISTINCT Xs /\ LENGTH Ps = LENGTH Xs /\
                EVERY (\e. X NOTIN (FV e)) Ps /\
                DISJOINT (set Xs) (FV P) ==>
               !E. fromPairs (X::Xs) (P::Ps) ' E = [P/X] (fromPairs Xs Ps ' E)
Proof
    rpt STRIP_TAC
 >> Know `fromPairs (X::Xs) (P::Ps) = (fromPairs Xs Ps) |+ (X,P)`
 >- (MATCH_MP_TAC fromPairs_HD >> art [])
 >> Rewr'
 >> MATCH_MP_TAC lemma0
 >> fs [FDOM_fromPairs, FEVERY_DEF]
 >> RW_TAC std_ss []
 >> rename1 `MEM Y Xs`
 >> `?n. n < LENGTH Xs /\ (Y = EL n Xs)` by PROVE_TAC [MEM_EL]
 >> fs [fromPairs_FAPPLY_EL, EVERY_MEM]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> rw [MEM_EL]
 >> Q.EXISTS_TAC `n` >> art []
QED

(* fromPairs_reduce in another form *)
Theorem lemma1[local] :
   !E E' map.
      map <> [] /\
      ~MEM (FST (HD map)) (MAP FST (TL map)) /\
      ALL_DISTINCT (MAP FST (TL map)) /\
      DISJOINT (set (MAP FST (TL map))) (FV (SND (HD map))) /\
      EVERY (\e. (FST (HD map)) NOTIN (FV e)) (MAP SND (TL map)) /\
      (FEMPTY |++ (TL map)) ' E = E'
   ==>
      (FEMPTY |++ map) ' E = [SND (HD map)/FST (HD map)] E'
Proof
    rpt GEN_TAC
 >> Cases_on `map` >- SRW_TAC [] []
 >> RW_TAC std_ss [HD, TL]
 >> Cases_on `h` >> fs []
 >> Q.ABBREV_TAC `Xs = FST (UNZIP t)`
 >> Q.ABBREV_TAC `Ps = SND (UNZIP t)`
 >> Know `t = ZIP (Xs,Ps)`
 >- (qunabbrevl_tac [`Xs`, `Ps`] >> fs [])
 >> Know `LENGTH Ps = LENGTH Xs`
 >- (qunabbrevl_tac [`Xs`, `Ps`] >> fs [])
 >> RW_TAC std_ss []
 >> Know `(MAP FST (ZIP (Xs,Ps))) = Xs` >- PROVE_TAC [MAP_ZIP]
 >> DISCH_THEN (fs o wrap)
 >> Know `(MAP SND (ZIP (Xs,Ps))) = Ps` >- PROVE_TAC [MAP_ZIP]
 >> DISCH_THEN (fs o wrap)
 >> rename1 ‘~MEM X Xs’
 >> MP_TAC (REWRITE_RULE [fromPairs_def]
                         (Q.SPECL [`X`,`Xs`,`r`,`Ps`] fromPairs_reduce))
 >> simp []
QED

(* Let map = ZIP(Xs,Ps), to convert ssub to a folding of CCS_Subst, each P
   of Ps must contains free variables up to the corresponding X of Xs.
 *)
Theorem lemma2[local] :
    !E map. ALL_DISTINCT (MAP FST map) /\
            EVERY (\(x,p). DISJOINT (set (MAP FST map)) (FV p)) map ==>
           (ssub (FEMPTY |++ map) E =
            FOLDR (\l e. [SND l/FST l] e) E map)
Proof
    GEN_TAC >> Induct_on `map`
 >- SRW_TAC [] [FUPDATE_LIST_THM, ssub_FEMPTY]
 >> rpt STRIP_TAC >> fs [MAP]
 >> MP_TAC (Q.SPECL [`E`, `ssub (FEMPTY |++ map) E`,
                     `h::map`] lemma1) >> fs []
 >> Know ‘DISJOINT (set (MAP FST map)) (FV (SND h)) /\
          EVERY (\e. FST h # e) (MAP SND map)’
 >- (Cases_on ‘h’ >> fs [] \\
     Q.PAT_X_ASSUM ‘EVERY (\(x,p). DISJOINT (set (MAP FST map)) (FV p) /\ q # p) map’
       MP_TAC >> rw [EVERY_MEM, MEM_MAP] \\
     Q.PAT_X_ASSUM ‘!e. MEM e map ==> _’ (MP_TAC o (Q.SPEC ‘y’)) \\
     Cases_on ‘y’ >> rw [])
 >> rw []
 >> Cases_on `h` >> fs []
 >> rename1 `X # P`
 >> Suff ‘ssub (FEMPTY |++ map) E =
          FOLDR (\l e. [SND l/FST l] e) E map’ >- rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.PAT_X_ASSUM
     ‘EVERY (\(x,p). DISJOINT (set (MAP FST map)) (FV p) /\ X # p) map’ MP_TAC
 >> rw [EVERY_MEM]
 >> Q.PAT_X_ASSUM ‘!e. MEM e map ==> _’ (MP_TAC o (Q.SPEC ‘e’))
 >> Cases_on ‘e’ >> rw []
QED

(* lemma2 in another form; this is less general than fromPairs_reduce *)
Theorem fromPairs_FOLDR :
    !Xs Ps E. ALL_DISTINCT Xs /\ LENGTH Ps = LENGTH Xs /\
              EVERY (\p. DISJOINT (set Xs) (FV p)) Ps ==>
              (fromPairs Xs Ps) ' E =
              FOLDR (\(x,y) e. [y/x] e) E (ZIP (Xs,Ps))
Proof
    RW_TAC std_ss []
 >> MP_TAC (Q.SPECL [`E`, `ZIP (Xs,Ps)`] lemma2)
 >> RW_TAC std_ss [MAP_ZIP, fromPairs_def]
 >> Know `(\l e. [SND l/FST l] e) = (\(x,y) e. [y/x] e)`
 >- (rw [FUN_EQ_THM] >> Cases_on `l` >> rw [])
 >> DISCH_THEN (fs o wrap)
 >> POP_ASSUM MATCH_MP_TAC
 >> POP_ASSUM MP_TAC >> rw [EVERY_MEM, MEM_ZIP]
 >> simp []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> rw [MEM_EL]
 >> Q.EXISTS_TAC ‘n’ >> art []
QED

Theorem fromPairs_ISUB :
    !Xs Ps E. ALL_DISTINCT Xs /\ LENGTH Ps = LENGTH Xs /\
              EVERY (\p. DISJOINT (set Xs) (FV p)) Ps ==>
              (fromPairs Xs Ps) ' E = E ISUB REVERSE (ZIP (Ps,Xs))
Proof
    Induct_on ‘Xs’
 >- rw [fromPairs_def, FUPDATE_LIST_THM]
 >> rw []
 >> Cases_on ‘Ps’ >- fs []
 >> fs [fromPairs_def] >> rename1 ‘v # P’
 (* RHS rewriting *)
 >> REWRITE_TAC [GSYM ISUB_APPEND, GSYM SUB_ISUB_SINGLETON]
 (* LHS rewriting *)
 >> rw [fromPairs_def, FUPDATE_LIST_THM]
 >> Know ‘(FEMPTY :string |-> term) |+ (v,P) |++ ZIP (Xs,t) =
          (FEMPTY |++ ZIP (Xs,t)) |+ (v,P)’
 >- (MATCH_MP_TAC FUPDATE_FUPDATE_LIST_COMMUTES \\
     rw [MAP_ZIP])
 >> Rewr'
 >> qabbrev_tac ‘fm = (FEMPTY :string |-> term) |++ ZIP (Xs,t)’
 >> ‘FDOM fm = set Xs’ by rw [Abbr ‘fm’, FDOM_FUPDATE_LIST, MAP_ZIP]
 (* applying ssub_update_apply_SUBST' *)
 >> Know ‘(fm |+ (v,P)) ' E = [fm ' P/v] (fm ' E)’
 >- (MATCH_MP_TAC ssub_update_apply_SUBST' >> rw [] \\
    ‘fm = fromPairs Xs t’ by rw [Abbr ‘fm’, fromPairs_def] \\
     POP_ORW \\
     Q.PAT_X_ASSUM ‘MEM k Xs’ MP_TAC >> rw [MEM_EL] \\
     Know ‘fromPairs Xs t ' (EL n Xs) = EL n t’
     >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘EVERY _ t’ MP_TAC >> rw [EVERY_MEM, MEM_EL] \\
     POP_ASSUM (MP_TAC o (Q.SPEC ‘EL n t’)) \\
     impl_tac >- (Q.EXISTS_TAC ‘n’ >> art []) \\
     rw [DISJOINT_ALT'])
 >> Rewr'
 >> Know ‘fm ' P = P’
 >- (MATCH_MP_TAC ssub_14b \\
     rw [GSYM DISJOINT_DEF, Once DISJOINT_SYM])
 >> Rewr'
 >> Suff ‘fm ' E = E ISUB REVERSE (ZIP (t,Xs))’ >- rw []
 >> qunabbrev_tac ‘fm’
 >> FIRST_X_ASSUM irule >> rw []
 >> fs [EVERY_CONJ]
QED

Theorem fromPairs_self :
    !E Xs. ALL_DISTINCT Xs ==> fromPairs Xs (MAP VAR Xs) ' E = E
Proof
    Q.X_GEN_TAC ‘E’
 >> Induct_on `Xs`
 >> SRW_TAC [] [ssub_FEMPTY, fromPairs_EMPTY]
 >> Q.PAT_X_ASSUM `ALL_DISTINCT Xs ==> _` MP_TAC
 >> RW_TAC std_ss []
 >> MP_TAC (Q.SPECL [`h`, `Xs`, `VAR h`, `MAP VAR Xs`] fromPairs_reduce)
 >> `LENGTH (MAP VAR Xs) = LENGTH Xs` by PROVE_TAC [LENGTH_MAP]
 >> simp []
 >> Suff ‘EVERY (\e. h # e) (MAP VAR Xs)’
 >- RW_TAC std_ss [EVERY_MEM, MEM_MAP]
 >> rw [EVERY_MAP, EVERY_MEM, FV_thm]
QED

Theorem fromPairs_nested :
    !Xs Ps Es E.
        ALL_DISTINCT Xs /\ LENGTH Ps = LENGTH Xs /\ LENGTH Es = LENGTH Xs ==>
        fromPairs Xs Ps ' (fromPairs Xs Es ' E) =
        fromPairs Xs (MAP ($' (fromPairs Xs Ps)) Es) ' E
Proof
    Suff (* rewriting for induction *)
   `!Xs Ps Es. ALL_DISTINCT Xs /\
              (LENGTH Ps = LENGTH Xs) /\ (LENGTH Es = LENGTH Xs) ==>
        !E. fromPairs Xs Ps ' (fromPairs Xs Es ' E) =
            fromPairs Xs (MAP ($' (fromPairs Xs Ps)) Es) ' E`
 >- METIS_TAC []
 >> rpt GEN_TAC >> STRIP_TAC
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> qabbrev_tac ‘fm2 = fromPairs Xs Ps’
 >> Q.EXISTS_TAC ‘set Xs UNION BIGUNION (IMAGE FV (set Es))
                         UNION BIGUNION (IMAGE FV (set Ps))
                         UNION BIGUNION (IMAGE (\e. FV (ssub fm2 e)) (set Es))’
 >> rw [Abbr ‘fm2’, FDOM_fromPairs] (* 5 subgoals *)
 >> TRY (rw [FINITE_FV]) (* 2 subgoals left *)
 >- (fs [MEM_EL] >> rename1 `X = EL n Xs` \\
    `LENGTH (MAP (ssub (fromPairs Xs Ps)) Es) = LENGTH Xs`
       by PROVE_TAC [LENGTH_MAP] \\
     ASM_SIMP_TAC std_ss [fromPairs_FAPPLY_EL, EL_MAP])
 >> `LENGTH (MAP (ssub (fromPairs Xs Ps)) Es) = LENGTH Xs`
       by PROVE_TAC [LENGTH_MAP]
 (* stage work *)
 >> qabbrev_tac ‘fm1 = fromPairs Xs Es’
 >> qabbrev_tac ‘fm2 = fromPairs Xs Ps’
 (* applying ssub_rec *)
 >> Know ‘ssub fm1 (LAM y E) = LAM y (ssub fm1 E)’
 >- (MATCH_MP_TAC ssub_LAM >> rw [Abbr ‘fm1’, FDOM_fromPairs] \\
     fs [MEM_EL] >> rename1 `X = EL n Xs` \\
     ASM_SIMP_TAC std_ss [fromPairs_FAPPLY_EL, EL_MAP] \\
     METIS_TAC [])
 >> Rewr'
 >> Know ‘ssub fm2 (LAM y (ssub fm1 E)) =
          LAM y (ssub fm2 (ssub fm1 E))’
 >- (MATCH_MP_TAC ssub_LAM >> rw [Abbr ‘fm2’, FDOM_fromPairs] \\
     fs [MEM_EL] >> rename1 `X = EL n Xs` \\
     ASM_SIMP_TAC std_ss [fromPairs_FAPPLY_EL, EL_MAP] \\
     METIS_TAC [])
 >> Rewr'
 >> qabbrev_tac ‘fm3 = fromPairs Xs (MAP (ssub fm2) Es)’
 >> Know ‘ssub fm3 (LAM y E) = LAM y (ssub fm3 E)’
 >- (MATCH_MP_TAC ssub_LAM >> rw [Abbr ‘fm3’, FDOM_fromPairs] \\
     FULL_SIMP_TAC std_ss [MEM_EL] >> rename1 `X = EL n Xs` \\
     ASM_SIMP_TAC std_ss [fromPairs_FAPPLY_EL, EL_MAP] \\
     (* NOTE: this is why we put
          ‘BIGUNION (IMAGE (\e. FV (ssub fm2 e)) (set Es))’
        into the exclusive set required by nc_INDUCTION2. *)
     METIS_TAC [])
 >> Rewr'
 >> rw [LAM_eq_thm]
QED

(* A (non-trivial) generalization of FV_SUBSET *)
Theorem FV_fromPairs :
    !Xs Ps E. ALL_DISTINCT Xs /\ LENGTH Ps = LENGTH Xs ==>
              FV (fromPairs Xs Ps ' E) SUBSET
                 (FV E) UNION BIGUNION (IMAGE FV (set Ps))
Proof
    NTAC 2 GEN_TAC
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘set Xs UNION BIGUNION (IMAGE FV (set Ps))’
 >> rw [FDOM_fromPairs, ssub_thm] (* 7 subgoals *)
 >- (fs [MEM_EL, fromPairs_FAPPLY_EL] \\
    `MEM (EL n Ps) Ps` by PROVE_TAC [MEM_EL] >> ASM_SET_TAC [])
 >> TRY (rw [FINITE_FV] >> ASM_SET_TAC [])
 >> qabbrev_tac ‘fm = fromPairs Xs Ps’
 >> Know ‘ssub fm (LAM y E) = LAM y (ssub fm E)’
 >- (MATCH_MP_TAC ssub_LAM \\
     rw [Abbr ‘fm’, FDOM_fromPairs] \\
     fs [MEM_EL, fromPairs_FAPPLY_EL] \\
     METIS_TAC [])
 >> Rewr'
 >> fs [FV_thm]
 >> qabbrev_tac ‘A = ssub fm E’
 >> qabbrev_tac ‘B = BIGUNION (IMAGE FV (set Ps))’
 >> Q.PAT_X_ASSUM ‘FV A SUBSET FV E UNION B’ MP_TAC
 >> SET_TAC []
QED

(* A more precise estimation with `set Xs` *)
Theorem FV_fromPairs' :
    !Xs Ps E. ALL_DISTINCT Xs /\ LENGTH Ps = LENGTH Xs ==>
              FV (fromPairs Xs Ps ' E) SUBSET
                 ((FV E) DIFF (set Xs)) UNION BIGUNION (IMAGE FV (set Ps))
Proof
    NTAC 2 GEN_TAC
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘set Xs UNION BIGUNION (IMAGE FV (set Ps))’
 >> rw [FDOM_fromPairs, ssub_thm] (* 7 subgoals *)
 >- (fs [MEM_EL, fromPairs_FAPPLY_EL] \\
    `MEM (EL n Ps) Ps` by PROVE_TAC [MEM_EL] >> ASM_SET_TAC [])
 >> TRY (rw [FINITE_FV] >> ASM_SET_TAC [])
 >> qabbrev_tac ‘fm = fromPairs Xs Ps’
 >> Know ‘ssub fm (LAM y E) = LAM y (ssub fm E)’
 >- (MATCH_MP_TAC ssub_LAM \\
     rw [Abbr ‘fm’, FDOM_fromPairs] \\
     fs [MEM_EL, fromPairs_FAPPLY_EL] \\
     METIS_TAC []) >> Rewr'
 >> fs [FV_thm]
 >> qabbrev_tac ‘A = fm ' E’
 >> qabbrev_tac ‘B = BIGUNION (IMAGE FV (set Ps))’
 >> Q.PAT_X_ASSUM ‘FV A SUBSET FV E DIFF set Xs UNION B’ MP_TAC
 >> SET_TAC []
QED

(* If, additionally, ‘ALL_DISTINCT xs /\ DISJOINT (set xs) (set ys)’ holds,
   the REVERSE in conclusion can be eliminated.
 *)
Theorem fresh_tpm_isub' :
    !xs ys t. LENGTH xs = LENGTH ys /\
              ALL_DISTINCT xs /\ ALL_DISTINCT ys /\
              DISJOINT (set xs) (set ys) /\
              DISJOINT (set ys) (FV t)
          ==> tpm (ZIP (xs,ys)) t = t ISUB (ZIP (MAP VAR ys, xs))
Proof
    rw [fresh_tpm_isub]
 >> qabbrev_tac ‘Ps = MAP VAR ys’
 >> ‘LENGTH Ps = LENGTH ys’ by rw [Abbr ‘Ps’]
 >> simp [MAP_REVERSE, GSYM REVERSE_ZIP]
 (* applying fromPairs_ISUB *)
 >> Know ‘t ISUB REVERSE (ZIP (Ps,xs)) = fromPairs xs Ps ' t’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC fromPairs_ISUB >> art [] \\
     rw [EVERY_MEM, MEM_EL, Abbr ‘Ps’] \\
     simp [EL_MAP] \\
     Q.PAT_X_ASSUM ‘DISJOINT (set xs) (set ys)’ MP_TAC \\
     rw [DISJOINT_ALT'] \\
     POP_ASSUM MATCH_MP_TAC >> simp [EL_MEM])
 >> Rewr'
 >> qabbrev_tac ‘xs' = REVERSE xs’
 >> qabbrev_tac ‘Ps' = REVERSE Ps’
 >> ‘xs = REVERSE xs' /\ Ps = REVERSE Ps'’ by rw [Abbr ‘xs'’, Abbr ‘Ps'’]
 >> NTAC 2 POP_ORW
 >> ‘LENGTH xs' = LENGTH xs /\ LENGTH Ps' = LENGTH Ps’
      by rw [Abbr ‘xs'’, Abbr ‘Ps'’]
 >> simp [GSYM REVERSE_ZIP]
 >> Know ‘t ISUB REVERSE (ZIP (Ps',xs')) = fromPairs xs' Ps' ' t’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC fromPairs_ISUB >> art [] \\
     CONJ_TAC >- rw [Abbr ‘xs'’, ALL_DISTINCT_REVERSE] \\
     rw [EVERY_MEM, MEM_EL, Abbr ‘Ps'’, Abbr ‘Ps’, Abbr ‘xs'’] \\
     simp [EL_MAP] \\
     Q.PAT_X_ASSUM ‘DISJOINT (set xs) (set ys)’ MP_TAC \\
     rw [DISJOINT_ALT'] \\
     POP_ASSUM MATCH_MP_TAC >> simp [EL_MEM])
 >> Rewr'
 >> simp [fromPairs_def, Abbr ‘xs'’, Abbr ‘Ps'’]
 >> qabbrev_tac ‘fm = FEMPTY |++ ZIP (xs,Ps)’
 >> qabbrev_tac ‘fm' = FEMPTY |++ ZIP (REVERSE xs,REVERSE Ps)’
 >> Suff ‘fm = fm'’ >- rw []
 >> ‘FDOM fm = set xs /\ FDOM fm' = set xs’
       by rw [Abbr ‘fm’, Abbr ‘fm'’, GSYM fromPairs_def, FDOM_fromPairs,
              LIST_TO_SET_REVERSE]
 >> rw [fmap_EXT, MEM_EL]
 (* applying fromPairs_FAPPLY_EL *)
 >> simp [Abbr ‘fm’, Abbr ‘fm'’, GSYM fromPairs_def]
 >> Know ‘fromPairs xs Ps ' (EL n xs) = EL n Ps’
 >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> art [])
 >> Rewr'
 >> qabbrev_tac ‘xs' = REVERSE xs’
 >> qabbrev_tac ‘Ps' = REVERSE Ps’
 >> ‘xs = REVERSE xs' /\ Ps = REVERSE Ps'’ by rw [Abbr ‘xs'’, Abbr ‘Ps'’]
 >> NTAC 2 POP_ORW
 >> ‘LENGTH xs' = LENGTH xs /\ LENGTH Ps' = LENGTH Ps’
      by rw [Abbr ‘xs'’, Abbr ‘Ps'’]
 >> simp [EL_REVERSE, Once EQ_SYM_EQ]
 >> MATCH_MP_TAC fromPairs_FAPPLY_EL
 >> simp [Abbr ‘xs'’, Abbr ‘Ps'’, ALL_DISTINCT_REVERSE]
QED

(*****************************************************************************)
(*  Simultaneous substitution given by a function containing infinite keys   *)
(*                                                                           *)
(*  NOTE: This definition is not used (it doesn't have finite "support").    *)
(*****************************************************************************)

Definition fssub_def :
    fssub f t = FUN_FMAP f (FV t) ' t
End

(*---------------------------------------------------------------------------*
 *  ‘tpm’ as an equivalence relation between terms
 *---------------------------------------------------------------------------*)

Definition tpm_rel_def :
    tpm_rel M N = ?pi. tpm pi M = N
End

Theorem tpm_rel_alt :
    !M N. tpm_rel M N <=> ?pi. M = tpm pi N
Proof
    rw [tpm_rel_def]
 >> EQ_TAC >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      fs [tpm_eql] >> Q.EXISTS_TAC ‘REVERSE pi’ >> rw [],
      (* goal 2 (of 2) *)
      fs [tpm_eqr] >> Q.EXISTS_TAC ‘REVERSE pi’ >> rw [] ]
QED

Theorem equivalence_tpm_rel :
    equivalence tpm_rel
Proof
    rw [equivalence_def, reflexive_def, symmetric_def, transitive_def]
 >| [ (* goal 1 (of 3) *)
      rw [tpm_rel_def] >> Q.EXISTS_TAC ‘[]’ >> rw [],
      (* goal 2 (of 3) *)
      rw [tpm_rel_def] >> EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
      [ (* goal 2.1 (of 2) *)
        ONCE_REWRITE_TAC [EQ_SYM_EQ] >> fs [tpm_eql] \\
        Q.EXISTS_TAC ‘REVERSE pi’ >> rw [],
        (* goal 2.2 (of 2) *)
        ONCE_REWRITE_TAC [EQ_SYM_EQ] >> fs [tpm_eql] \\
        Q.EXISTS_TAC ‘REVERSE pi’ >> rw [] ],
      (* goal 3 (of 3) *)
      fs [tpm_rel_def] \\
      POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
      POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
      Q.EXISTS_TAC ‘pi' ++ pi’ \\
      rw [pmact_decompose] ]
QED

val tpm_rel_thm = equivalence_tpm_rel |>
    REWRITE_RULE [equivalence_def, reflexive_def, symmetric_def, transitive_def];

(* below are easy-to-use forms of [equivalence_tpm_rel] *)
Theorem tpm_rel_REFL[simp] :
    tpm_rel M M
Proof
    rw [tpm_rel_thm]
QED

Theorem tpm_rel_SYM :
    !M N. tpm_rel M N ==> tpm_rel N M
Proof
    rw [tpm_rel_thm]
QED

Theorem tpm_rel_SYM_EQ :
    !M N. tpm_rel M N <=> tpm_rel N M
Proof
    rw [tpm_rel_thm]
QED

Theorem tpm_rel_TRANS :
    !M1 M2 M3. tpm_rel M1 M2 /\ tpm_rel M2 M3 ==> tpm_rel M1 M3
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC (cj 3 tpm_rel_thm)
 >> Q.EXISTS_TAC ‘M2’ >> art []
QED

Theorem tpm_rel_tpm[simp] :
    tpm_rel (tpm pi M) M /\ tpm_rel M (tpm pi M)
Proof
    CONJ_ASM1_TAC
 >- (REWRITE_TAC [tpm_rel_alt] \\
     Q.EXISTS_TAC ‘pi’ >> REWRITE_TAC [])
 >> MATCH_MP_TAC tpm_rel_SYM >> art []
QED

Theorem tpm_rel_cong :
    !M M' N N'. tpm_rel M M' /\ tpm_rel N N' ==> (tpm_rel M N <=> tpm_rel M' N')
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC tpm_rel_TRANS >> Q.EXISTS_TAC ‘N’ >> art [] \\
      MATCH_MP_TAC tpm_rel_TRANS >> Q.EXISTS_TAC ‘M’ >> art [] \\
      MATCH_MP_TAC tpm_rel_SYM >> art [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC tpm_rel_TRANS >> Q.EXISTS_TAC ‘M'’ >> art [] \\
      MATCH_MP_TAC tpm_rel_TRANS >> Q.EXISTS_TAC ‘N'’ >> art [] \\
      MATCH_MP_TAC tpm_rel_SYM >> art [] ]
QED

(* ----------------------------------------------------------------------
    Set up the recursion functionality in binderLib
   ---------------------------------------------------------------------- *)

val lemma = prove(
  ``(∀x y t. pmact apm [(x,y)] (h t) = h (tpm [(x,y)] t)) <=>
     ∀pi t. pmact apm pi (h t) = h (tpm pi t)``,
  simp_tac (srw_ss()) [EQ_IMP_THM] >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
  strip_tac >> Induct_on `pi` >>
  asm_simp_tac (srw_ss()) [pmact_nil, FORALL_PROD] >>
  srw_tac [][Once tpm_CONS] >> srw_tac [][GSYM pmact_decompose]);

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
    \        pm_constant = ``nomset$mk_pmact term$raw_tpm``,\n\
    \        fv_rewrites = [],\n\
    \        recursion_thm = SOME tm_recursion_nosideset,\n\
    \        binders = [(``term$LAM``, 0, tpm_ALPHA)]}\n\
    \val _ = type_db :=\n\
    \          Binarymap.insert(!type_db,\n\
    \                           {Name = \"term\",Thy=\"term\"},\n\
    \                           term_info)\n\
    \in end;\n"

val _ = adjoin_after_completion (fn _ => PP.add_string term_info_string)


val _ = export_theory()
val _ = html_theory "term";
