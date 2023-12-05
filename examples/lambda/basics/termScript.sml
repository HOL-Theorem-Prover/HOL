open HolKernel Parse boolLib bossLib;

open boolSimps arithmeticTheory pred_setTheory finite_mapTheory hurdUtils;

open generic_termsTheory binderLib nomsetTheory nomdatatype;

val _ = new_theory "term";

val _ = set_fixity "=" (Infix(NONASSOC, 450))

val tyname = "term"

val vp = ``(λn u:unit. n = 0)``
val lp = ``(λn (d:unit + unit) tns uns.
               (n = 0) ∧ ISL d ∧ (tns = []) ∧ (uns = [0;0]) ∨
               (n = 0) ∧ ISR d ∧ (tns = [0]) ∧ (uns = []))``

val {term_ABS_pseudo11, term_REP_11, genind_term_REP, genind_exists,
     termP, absrep_id, repabs_pseudo_id, term_REP_t, term_ABS_t, newty, ...} =
    new_type_step1 tyname 0 {vp=vp, lp = lp}
val [gvar,glam] = genind_rules |> SPEC_ALL |> CONJUNCTS

val LAM_t = mk_var("LAM", ``:string -> ^newty -> ^newty``)
val LAM_def = new_definition(
  "LAM_def",
  ``^LAM_t v t = ^term_ABS_t (GLAM v (INR ()) [^term_REP_t t] [])``)
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

val tpm_name_pfx = "t"
val {tpm_thm, term_REP_tpm, t_pmact_t, tpm_t} =
    define_permutation {name_pfx = "t", name = tyname,
                        term_REP_t = term_REP_t,
                        term_ABS_t = term_ABS_t, absrep_id = absrep_id,
                        repabs_pseudo_id = repabs_pseudo_id,
                        cons_info = cons_info, newty = newty,
                        genind_term_REP = genind_term_REP}

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

(* exactly mimic historical bound variable names etc for backwards
   compatibility *)
val nc_INDUCTION2 = store_thm(
  "nc_INDUCTION2",
  ``∀P X.
      (∀s. P (VAR s)) ∧
      (∀t u. P t ∧ P u ==> P (APP t u)) ∧
      (∀y u. y ∉ X ∧ P u ==> P (LAM y u)) ∧ FINITE X ==>
      ∀u. P u``,
  metis_tac [mkX_ind term_ind]);


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
  ``λ(v:string) (u:unit + unit) (ds1:(ρ -> α) list) (ds2:(ρ -> α)  list)
                                (ts1:^repty' list) (ts2:^repty' list) (p:ρ).
       if ISR u then tlf (HD ds1) v (term_ABS (HD ts1)) p: α
       else taf (HD ds2) (HD (TL ds2)) (term_ABS (HD ts2))
                (term_ABS (HD (TL ts2))) p: α``
val tvf = ``λ(s:string) (u:unit) (p:ρ). tvf s p : α``

val LENGTH_NIL' =
    CONV_RULE (BINDER_CONV (LAND_CONV (REWR_CONV EQ_SYM_EQ)))
              listTheory.LENGTH_NIL
val LENGTH1 = prove(
  ``(1 = LENGTH l) ⇔ ∃e. l = [e]``,
  Cases_on `l` >> srw_tac [][listTheory.LENGTH_NIL]);
val LENGTH2 = prove(
  ``(2 = LENGTH l) ⇔ ∃a b. l = [a;b]``,
  Cases_on `l` >> srw_tac [][LENGTH1]);

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
                               LENGTH_NIL', LENGTH1, LENGTH2]
      |> ONCE_REWRITE_RULE [termP0]
      |> SIMP_RULE (srw_ss() ++ DNF_ss) [LENGTH1, LENGTH2,
                                         listTheory.LENGTH_NIL]
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
      |> Q.INST_TYPE [`:ρ` |-> `:unit`]
      |> Q.INST [`ppm` |-> `discrete_pmact`, `vr` |-> `λs u. vru s`,
                 `ap` |-> `λr1 r2 t1 t2 u. apu (r1()) (r2()) t1 t2`,
                 `lm` |-> `λr v t u. lmu (r()) v t`]
      |> SIMP_RULE (srw_ss()) [FORALL_ONE, FORALL_ONE_FN, EXISTS_ONE_FN,
                               fnpm_def]
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

(* NOTE: this theorem doesn't really belong here but moving it to basic_swapTheory
         seems unnecessary (and NEW_TAC is not available).
 *)
Theorem FRESH_lists :
    !n s : string set.
       FINITE s ==> ?l'. ALL_DISTINCT l' /\ DISJOINT (LIST_TO_SET l') s /\
                         (LENGTH l' = n)
Proof
  Induct THEN SRW_TAC [][] THENL [
    RES_TAC THEN
    Q_TAC (NEW_TAC "z") `LIST_TO_SET l' UNION s` THEN
    Q.EXISTS_TAC `z::l'` THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]
QED

(* ‘FRESH_list’ is a function for generating fresh list of new variables *)
local
    val th = SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] FRESH_lists
in
    val FRESH_list_def = new_specification ("FRESH_list_def", ["FRESH_list"], th)
end

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

val tpm_eqr = store_thm(
  "tpm_eqr",
  ``(t = tpm pi u) = (tpm (REVERSE pi) t = u)``,
  METIS_TAC [pmact_inverse]);

val tpm_CONS = store_thm(
  "tpm_CONS",
  ``tpm ((x,y)::pi) t = tpm [(x,y)] (tpm pi t)``,
  SRW_TAC [][GSYM pmact_decompose]);

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
        |> CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss()) [pairTheory.FORALL_PROD]))
        |> SIMP_RULE (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def,
                                 tpm_COND, tpm_fresh, pmact_sing_inv,
                                 basic_swapTheory.swapstr_eq_left]
        |> SIMP_RULE (srw_ss()) [rewrite_pairing, pairTheory.FORALL_PROD]
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

(* ----------------------------------------------------------------------
    Results about substitution
   ---------------------------------------------------------------------- *)

Theorem fresh_tpm_subst:
  !t. ~(u IN FV t) ==> (tpm [(u,v)] t = [VAR u/v] t)
Proof
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem tpm_subst:
  !N. tpm pi ([M/v] N) = [tpm pi M/lswapstr pi v] (tpm pi N)
Proof
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `v INSERT FV M` THEN
  SRW_TAC [][SUB_THM, SUB_VAR] THEN
  MATCH_MP_TAC (SUB_THM |> CONJUNCTS |> C (curry List.nth) 3 |> GSYM) THEN
  SRW_TAC [][stringpm_raw]
QED

Theorem tpm_subst_out:
  [M/v] (tpm pi N) = tpm pi ([tpm (REVERSE pi) M/lswapstr (REVERSE pi) v] N)
Proof SRW_TAC [][tpm_subst]
QED

Theorem lemma14a[simp]:
  !t. [VAR v/v] t = t
Proof
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem lemma14b:
  !M. ~(v IN FV M) ==> ([N/v] M = M)
Proof
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `v INSERT FV N` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem lemma14c:
  !t x u. x IN FV u ==> (FV ([t/x]u) = FV t UNION (FV u DELETE x))
Proof
  NTAC 2 GEN_TAC THEN HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `x INSERT FV t` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, EXTENSION] THEN
  METIS_TAC [lemma14b]
QED

Theorem FV_SUB:
  !t u v. FV ([t/v] u) = if v ∈ FV u then FV t ∪ (FV u DELETE v) else FV u
Proof PROVE_TAC [lemma14b, lemma14c]
QED

Theorem lemma15a:
  !M. v ∉ FV M ==> [N/v]([VAR v/x]M) = [N/x]M
Proof
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{x;v} UNION FV N` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem lemma15b:
  v ∉ FV M ==> [VAR u/v]([VAR v/u] M) = M
Proof SRW_TAC [][lemma15a]
QED

Theorem SUB_TWICE_ONE_VAR :
    !body. [x/v] ([y/v] body) = [[x/v]y / v] body
Proof
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN SRW_TAC [][SUB_THM, SUB_VAR] THEN
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
Theorem size_vsubst :
    !M:term. size ([VAR v/u] M) = size M
Proof
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
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

val _ = set_fixity "ISUB" (Infixr 501);

Definition DOM_DEF :
   (DOM [] = {}) /\
   (DOM ((x,y)::rst) = {y} UNION DOM rst)
End

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
 >> ASM_SIMP_TAC (srw_ss()) [ISUB_def, pairTheory.FORALL_PROD,
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
 >> ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, ISUB_def]
QED

(* moved here from standardisationScript.sml *)
Theorem ISUB_APP :
    !sub M N. (M @@ N) ISUB sub = (M ISUB sub) @@ (N ISUB sub)
Proof
    Induct
 >> ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, ISUB_def, SUB_THM]
QED

Theorem FOLDL_APP_ISUB :
    !args (t:term) sub.
         FOLDL APP t args ISUB sub =
         FOLDL APP (t ISUB sub) (MAP (\t. t ISUB sub) args)
Proof
    Induct >> SRW_TAC [][ISUB_APP]
QED

Theorem ISUB_VAR_FRESH :
    !y sub. ~MEM y (MAP SND sub) ==> (VAR y ISUB sub = VAR y)
Proof
    Q.X_GEN_TAC ‘x’
 >> Induct_on ‘sub’ >> rw [ISUB_def]
 >> Cases_on ‘h’ >> fs []
 >> rw [ISUB_def, SUB_VAR]
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
  ASM_SIMP_TAC (srw_ss())[ISUB_def, pairTheory.FORALL_PROD,
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
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `s INSERT FV M` THEN
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

Theorem ssub_14b:
  ∀t. (FV t ∩ FDOM phi = EMPTY) ==> ((phi : string |-> term) ' t = t)
Proof
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `fmFV phi` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, pred_setTheory.EXTENSION] THEN METIS_TAC []
QED

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
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘FDOM fm’
 >> rw [SUB_VAR, SUB_THM, ssub_thm]
 >> SET_TAC []
QED

Theorem fresh_ssub:
  ∀N. y ∉ FV N ∧ (∀k:string. k ∈ FDOM fm ⇒ y # fm ' k) ⇒ y # fm ' N
Proof
  ho_match_mp_tac nc_INDUCTION2 >>
  qexists ‘fmFV fm’ >>
  rw[] >> metis_tac[]
QED

Theorem ssub_SUBST:
  ∀M.
    (∀k. k ∈ FDOM fm ⇒ v # fm ' k) ∧ v ∉ FDOM fm ⇒
    fm ' ([N/v]M) = [fm ' N / v] (fm ' M)
Proof
  ho_match_mp_tac nc_INDUCTION2 >>
  qexists ‘fmFV fm ∪ {v} ∪ FV N’ >>
  rw[] >> rw[lemma14b, SUB_VAR] >>
  gvs[DECIDE “~p ∨ q ⇔ p ⇒ q”, PULL_FORALL] >>
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
 >> HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘v INSERT (FDOM fm UNION FV N)’
 >> rw [SUB_VAR, SUB_THM, ssub_thm, FAPPLY_FUPDATE_THM]
 >> TRY (METIS_TAC [])
 >- (MATCH_MP_TAC (GSYM lemma14b) \\
     METIS_TAC [NOT_IN_EMPTY])
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
    HO_MATCH_MP_TAC nc_INDUCTION2
 >> Q.EXISTS_TAC ‘v INSERT fmFV fm UNION FV M UNION FV N’
 >> rw [SUB_VAR, SUB_THM, ssub_thm, FAPPLY_FUPDATE_THM]
 >> TRY (METIS_TAC [])
 >- (MATCH_MP_TAC (GSYM ssub_14b) \\
     rw [GSYM DISJOINT_DEF, Once DISJOINT_SYM])
 >> Know ‘(fm |+ (v,N)) ' (LAM y M') = LAM y ((fm |+ (v,N)) ' M')’
 >- (MATCH_MP_TAC ssub_LAM >> rw [FAPPLY_FUPDATE_THM])
 >> Rewr'
 (* finally, applying IH *)
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

(* ----------------------------------------------------------------------
    Set up the recursion functionality in binderLib
   ---------------------------------------------------------------------- *)

val lemma = prove(
  ``(∀x y t. pmact apm [(x,y)] (h t) = h (tpm [(x,y)] t)) <=>
     ∀pi t. pmact apm pi (h t) = h (tpm pi t)``,
  simp_tac (srw_ss()) [EQ_IMP_THM] >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
  strip_tac >> Induct_on `pi` >>
  asm_simp_tac (srw_ss()) [pmact_nil, pairTheory.FORALL_PROD] >>
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
