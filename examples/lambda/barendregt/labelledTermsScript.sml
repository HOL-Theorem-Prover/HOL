open HolKernel boolLib Parse bossLib BasicProvers
open pred_setTheory

open binderLib
open basic_swapTheory nomsetTheory generic_termsTheory
open lcsymtacs
open nomdatatype
open boolSimps


val _ = new_theory "labelledTerms"

fun Store_thm(n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]
fun Save_thm(n,th) = save_thm(n,th) before export_rewrites [n]

val tyname = "lterm"

val vp = ``(λn u: unit. n = 0)``
val lp = ``(λn (d:unit + unit + num) tns uns.
               (n = 0) ∧ ISL d ∧ (tns = []) ∧ (uns = [0;0]) ∨
               (n = 0) ∧ ISR d ∧ ISL (OUTR d) ∧ (tns = [0]) ∧ (uns = []) ∨
               (n = 0) ∧ ISR d ∧ ISR (OUTR d) ∧ (tns = [0]) ∧ (uns = [0]))``

val {term_ABS_pseudo11, term_REP_11, genind_term_REP, genind_exists,
     termP, absrep_id, repabs_pseudo_id, newty, term_REP_t, term_ABS_t,...} =
    new_type_step1 tyname {vp=vp, lp = lp}

val _ = temp_overload_on ("termP", termP)

val [gvar,glam] = genind_rules |> SPEC_ALL |> CONJUNCTS
val qnewty = ty_antiq newty

fun defined_const th = th |> concl |> strip_forall |> #2 |> lhs |> repeat rator

val LAM_t = mk_var("LAM", ``:string -> ^newty -> ^newty``)
val LAM_def = new_definition(
  "LAM_def",
  ``^LAM_t v t = ^term_ABS_t (GLAM v (INR (INL ())) [^term_REP_t t] [])``);
val LAM_termP = prove(
  mk_comb(termP, LAM_def |> SPEC_ALL |> concl |> rhs |> rand),
  match_mp_tac glam >> srw_tac [][genind_term_REP])
val LAM_t = defined_const LAM_def

val LAMi_t = mk_var("LAMi", ``:num -> string -> ^newty -> ^newty -> ^newty``)
val LAMi_def = new_definition(
  "LAMi_def",
  ``^LAMi_t n v t1 t2 =
      ^term_ABS_t (GLAM v (INR (INR n)) [^term_REP_t t1] [^term_REP_t t2])``);
val LAMi_termP = prove(
  mk_comb(termP, LAMi_def |> SPEC_ALL |> concl |> rhs |> rand),
  match_mp_tac glam >> srw_tac [][genind_term_REP]);
val LAMi_t = defined_const LAMi_def

val APP_t = mk_var("APP", ``:^newty -> ^newty -> ^newty``)
val APP_pattern = ``GLAM v (INL ()) [] [^term_REP_t t1; ^term_REP_t t2]``
val APP_def = new_definition(
  "APP_def",
  ``^APP_t t1 t2 =
      ^term_ABS_t ^(subst [``v:string`` |-> ``ARB:string``] APP_pattern)``);
val APP_t = defined_const APP_def
val APP_termP = prove(
  mk_comb(termP, APP_pattern),
  match_mp_tac glam >> srw_tac [][genind_term_REP]);

val APP_def' = prove(
  ``^term_ABS_t ^APP_pattern = ^APP_t t1 t2``,
  srw_tac [][APP_def, GLAM_NIL_EQ, term_ABS_pseudo11, APP_termP]);


val VAR_t = mk_var("VAR", ``:string -> ^newty``)
val VAR_def = new_definition(
  "VAR_def",
  ``^VAR_t s = ^term_ABS_t (GVAR s ())``);
val VAR_termP = prove(
  mk_comb(termP, VAR_def |> SPEC_ALL |> concl |> rhs |> rand),
  match_mp_tac gvar >> srw_tac [][genind_term_REP]);
val VAR_t = defined_const VAR_def

(* tpm *)
val tpm_name = "ltpm"
val t = mk_var("lt", newty)
val tpm_t = mk_var(tpm_name, ``:^newty pm``)
val tpm_def = new_definition(
  tpm_name ^ "_def",
  ``^tpm_t pi ^t = ^term_ABS_t (gtpm pi (^term_REP_t ^t))``);
val tpm_t = tpm_def |> SPEC_ALL |> concl |> lhs |> repeat rator

val term_REP_tpm =
    tpm_def |> SPEC_ALL |> AP_TERM term_REP_t
             |> SIMP_RULE bool_ss [repabs_pseudo_id, genind_gtpm_eqn, genind_term_REP]

val tpm_is_perm = Store_thm(
  tpm_name ^ "_is_perm",
  ``is_perm ^tpm_t``,
  srw_tac [][is_perm_def, FUN_EQ_THM, tpm_def, gtpm_NIL,
             GSYM gtpm_compose, repabs_pseudo_id, absrep_id]
  >- srw_tac [][GSYM term_REP_tpm, absrep_id] >>
  AP_TERM_TAC >>
  (is_perm_def |> ISPEC ``generic_terms$gtpm`` |> C EQ_MP gtpm_is_perm
               |> CONJUNCTS |> last |> REWRITE_RULE [FUN_EQ_THM]
               |> MATCH_MP_TAC) >>
  POP_ASSUM ACCEPT_TAC)

fun tpm_clause contermP con_def =
  con_def |> SPEC_ALL
          |> Q.AP_TERM `^tpm_t pi`
          |> CONV_RULE (RAND_CONV (SIMP_CONV bool_ss [tpm_def]))
          |> SIMP_RULE std_ss [repabs_pseudo_id, contermP, gtpm_thm, listTheory.MAP,
                               listpm_def]
          |> SIMP_RULE bool_ss [GSYM con_def, GSYM term_REP_tpm]
          |> GEN_ALL

val tpm_thm = Save_thm(
  tpm_name ^ "_thm",
  LIST_CONJ [tpm_clause VAR_termP VAR_def,
             tpm_clause APP_termP (GSYM APP_def'),
             tpm_clause LAM_termP LAM_def,
             tpm_clause LAMi_termP LAMi_def]);


(* support *)
val term_REP_eqv = prove(
   ``support (fnpm ^tpm_t gtpm) ^term_REP_t {}`` ,
   srw_tac [][support_def, fnpm_def, FUN_EQ_THM, term_REP_tpm, gtpm_sing_inv]);

val supp_term_REP = prove(
  ``supp (fnpm ^tpm_t gtpm) ^term_REP_t = {}``,
  REWRITE_TAC [GSYM SUBSET_EMPTY] >> MATCH_MP_TAC (GEN_ALL supp_smallest) >>
  srw_tac [][gtpm_is_perm, tpm_is_perm, term_REP_eqv])

val supptpm_support = prove(
  ``support ^tpm_t ^t (supp gtpm (^term_REP_t ^t))``,
  srw_tac [][support_def, tpm_def, gtpm_fresh, absrep_id]);

val supptpm_apart = prove(
  ``x ∈ supp gtpm (^term_REP_t ^t) ∧ y ∉ supp gtpm (^term_REP_t ^t) ⇒
    ^tpm_t [(x,y)] ^t ≠ ^t``,
  srw_tac [][tpm_def]>>
  DISCH_THEN (MP_TAC o AP_TERM term_REP_t) >>
  srw_tac [][repabs_pseudo_id, genind_gtpm_eqn, genind_term_REP, supp_apart,
             gtpm_is_perm]);

val supp_tpm = prove(
  ``supp ^tpm_t ^t = supp gtpm (^term_REP_t ^t)``,
  match_mp_tac (GEN_ALL supp_unique_apart) >>
  srw_tac [][supptpm_support, supptpm_apart, FINITE_GFV, tpm_is_perm])

val _ = overload_on ("FV", ``supp ^tpm_t``)

val FINITE_FV = Store_thm(
  "FINITE_FV",
  ``FINITE (FV ^t)``,
  srw_tac [][supp_tpm, FINITE_GFV]);

fun supp_clause contermP con_def = let
  val t = mk_comb(``supp ^tpm_t``, lhand (concl (SPEC_ALL con_def)))
in
  t |> SIMP_CONV (srw_ss()) [supp_tpm, con_def, repabs_pseudo_id, contermP,
                             GFV_thm]
    |> SIMP_RULE (srw_ss()) [GSYM supp_tpm]
    |> GEN_ALL
end

val FV_thm = Save_thm(
  "FV_thm",
  LIST_CONJ
    [supp_clause VAR_termP VAR_def,
     supp_clause APP_termP APP_def,
     supp_clause LAM_termP LAM_def,
     supp_clause LAMi_termP LAMi_def]);


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
    bvc_genind |> INST_TYPE [alpha |-> ``:unit+unit+num``, beta |-> ``:unit``]
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
               |> Q.INST [`Q` |-> `λt. P (^term_ABS_t t)`]
               |> SIMP_RULE std_ss [GSYM LAM_def, APP_def', GSYM VAR_def, absrep_id,
                                    GSYM LAMi_def, GSYM supp_tpm]
               |> elim_unnecessary_atoms {finite_fv = FINITE_FV}
                                         [ASSUME ``!x:'c. FINITE (fv x:string set)``]
               |> SPEC_ALL |> UNDISCH
               |> genit |> DISCH_ALL |> Q.GEN `fv` |> Q.GEN `P`

fun mkX_ind th = th |> Q.SPEC `λt x. Q t` |> Q.SPEC `λx. X`
                    |> SIMP_RULE std_ss [] |> Q.GEN `X`
                    |> Q.INST [`Q` |-> `P`] |> Q.GEN `P`

val LAMi_eq_thm = save_thm(
  "lLAMi_eq_thm",
  ``^LAMi_t n1 v1 t1 u1 = ^LAMi_t n2 v2 t2 u2``
   |> SIMP_CONV (srw_ss()) [LAMi_def, LAMi_termP, term_ABS_pseudo11,
                            GLAM_eq_thm, term_REP_11, GSYM term_REP_tpm,
                            GSYM supp_tpm])

val LAM_eq_thm = save_thm(
  "lLAM_eq_thm",
  ``^LAM_t v1 t1 = ^LAM_t v2 t2``
   |> SIMP_CONV (srw_ss()) [LAM_def, LAM_termP, term_ABS_pseudo11,
                            GLAM_eq_thm, term_REP_11, GSYM term_REP_tpm,
                            GSYM supp_tpm])

val (_, repty) = dom_rng (type_of term_REP_t)
val repty' = ty_antiq repty

val tlf =
  ``λ(v:string) (u:unit + unit + num)
                (ds1:(ρ -> α) list) (ds2:(ρ -> α) list)
                (ts1:^repty' list) (ts2:^repty' list) (p:ρ).
       if ISL u then ap (HD ds2) (HD (TL ds2)) (^term_ABS_t (HD ts2))
                        (^term_ABS_t (HD (TL ts2))) p: α
       else if ISL (OUTR u) then
         lm (HD ds1) v (^term_ABS_t (HD ts1)) p: α
       else
         li (HD ds1) (HD ds2) (OUTR (OUTR u)) v
            (^term_ABS_t (HD ts1)) (^term_ABS_t (HD ts2)) p``
val tvf = ``λ(s:string) (u:unit) (p:ρ). vr' s p: α``

val termP0 = prove(
  ``genind ^vp ^lp n t <=> ^termP t ∧ (n = 0)``,
  EQ_TAC >> simp_tac (srw_ss()) [] >> strip_tac >>
  qsuff_tac `n = 0` >- (strip_tac >> srw_tac [][]) >>
  pop_assum mp_tac >>
  Q.ISPEC_THEN `t` STRUCT_CASES_TAC gterm_cases >>
  srw_tac [][genind_GVAR, genind_GLAM_eqn]);

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
    nomdatatype.termP_removal {repty = repty, termP = termP,
                               elimth = termP_elim, tpm_def = tpm_def,
                               absrep_id = absrep_id}

val cons_info =
    [{con_termP = VAR_termP, con_def = VAR_def},
     {con_termP = APP_termP, con_def = SYM APP_def'},
     {con_termP = LAM_termP, con_def = LAM_def},
     {con_termP = LAMi_termP, con_def = LAMi_def}]

val parameter_tm_recursion = save_thm(
  "parameter_ltm_recursion",
  parameter_gtm_recursion
        |> INST_TYPE [alpha |-> ``:unit + unit + num``, beta |-> ``:unit``,
                      gamma |-> alpha]
        |> Q.INST [`lf` |-> `^tlf`, `vf` |-> `^tvf`, `vp` |-> `^vp`,
                   `lp` |-> `^lp`, `n` |-> `0`]
        |> SIMP_RULE (srw_ss()) [sumTheory.FORALL_SUM, FORALL_AND_THM,
                                 GSYM RIGHT_FORALL_IMP_THM, IMP_CONJ_THM,
                                 GSYM RIGHT_EXISTS_AND_THM,
                                 GSYM LEFT_EXISTS_AND_THM,
                                 GSYM LEFT_FORALL_IMP_THM,
                                 LIST_REL_CONS1, genind_GVAR,
                                 genind_GLAM_eqn, NEWFCB_def,
                                 sidecond_def, relsupp_def,
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
                                  [ASSUME ``FINITE (A:string set)``]
        |> UNDISCH_ALL |> DISCH_ALL
        |> REWRITE_RULE [AND_IMP_INTRO]
        |> CONV_RULE (LAND_CONV (REWRITE_CONV [GSYM CONJ_ASSOC]))
        |> Q.INST [`vr'` |-> `vr`, `dpm` |-> `apm`])

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
      |> Q.INST [`ppm` |-> `K I`, `vr` |-> `λs u. vru s`,
                 `ap` |-> `λr1 r2 t1 t2 u. apu (r1()) (r2()) t1 t2`,
                 `lm` |-> `λr v t u. lmu (r()) v t`,
                 `li` |-> `λr1 r2 n v t1 t2 u. liu (r1()) (r2()) n v t1 t2`]
      |> SIMP_RULE (srw_ss()) [FORALL_ONE, FORALL_ONE_FN, EXISTS_ONE_FN,
                               fnpm_def]
      |> SIMP_RULE (srw_ss() ++ CONJ_ss) [supp_unitfn]
      |> Q.INST [`apu` |-> `ap`, `lmu` |-> `lm`, `vru` |-> `vr`,
                 `liu` |-> `li`])

val simple_induction = save_thm(
  "simple_lterm_induction",
  term_ind |> INST_TYPE [gamma |-> oneSyntax.one_ty]
           |> SPECL [``\t:lterm u:unit. P t:bool``, ``\x:unit. {}:string set``]
           |> SIMP_RULE bool_ss [FINITE_EMPTY, NOT_IN_EMPTY]
           |> GEN ``P:lterm -> bool``)

val lterm_bvc_induction = store_thm(
  "lterm_bvc_induction",
  ``!P X. FINITE X /\
          (!s. P (VAR s)) /\
          (!M N. P M /\ P N ==> P (APP M N)) /\
          (!v M. ~(v IN X) /\ P M ==> P (LAM v M)) /\
          (!n v M N. ~(v IN X) /\ ~(v IN FV N) /\ P M /\ P N ==>
                     P (LAMi n v M N)) ==>
          !t. P t``,
  rpt gen_tac >> strip_tac >> ho_match_mp_tac (mkX_ind term_ind) >>
  qexists_tac `X` >> srw_tac [][]);

val _ = Save_thm("ltpm_NIL", MATCH_MP is_perm_nil tpm_is_perm)
val _ = Save_thm("ltpm_sing_inv", MATCH_MP is_perm_sing_inv tpm_is_perm)
val _ = Save_thm("ltpm_id_front", MATCH_MP is_perm_id tpm_is_perm);
val _ = Save_thm("ltpm_inverse", MATCH_MP is_perm_inverse tpm_is_perm)
val FV_tpm = Save_thm("FV_" ^ tpm_name,
                      ``x ∈ FV (ltpm p lt)``
                      |> REWRITE_CONV [MATCH_MP perm_supp tpm_is_perm,
                                       MATCH_MP perm_IN perm_of_is_perm]
                      |> GEN_ALL)
val tpm_flip_args = save_thm("ltpm_flip_args", MATCH_MP is_perm_flip_args tpm_is_perm)
val ltpm_eql = save_thm("ltpm_eql", MATCH_MP is_perm_eql tpm_is_perm)
val _ = save_thm("ltpm_eqr",
                 CONV_RULE (BINOP_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
                           ltpm_eql)

val tpm_fresh = store_thm(
  "ltpm_fresh",
  ``∀t:lterm x y. x ∉ FV t ∧ y ∉ FV t ==> (ltpm [(x,y)] t = t)``,
  srw_tac [][supp_fresh])

val _ = set_mapped_fixity {tok = "@@", fixity = Infixl 901, term_name = "APP"}

val _ = Store_thm("lterm_distinct",
  ``VAR s ≠ t @@ u ∧ VAR s ≠ LAM v t ∧ VAR s ≠ LAMi n v t u ∧
    t @@ u ≠ LAM v t' ∧ t @@ u ≠ LAMi n v t1 t2 ∧
    LAM v t ≠ LAMi n w t1 t2``,
  srw_tac [][LAM_def, LAMi_def, VAR_def, APP_def, VAR_termP, APP_termP, LAM_termP,
             LAMi_termP, term_ABS_pseudo11, gterm_distinct, GLAM_eq_thm])

val _ = Store_thm("lterm_11",
   ``((VAR s1 = VAR s2) <=> (s1 = s2)) ∧
     ((t11 @@ t12 = t21 @@ t22) <=> (t11 = t21) ∧ (t12 = t22)) ∧
     ((LAM v t1 = LAM v t2) <=> (t1 = t2)) ∧
     ((LAMi n1 v t11 t12 = LAMi n2 v t21 t22) =
         (n1 = n2) ∧ (t11 = t21) ∧ (t12 = t22))``,
  srw_tac [][VAR_def, APP_def, LAM_def, LAM_termP, VAR_termP, APP_termP,
             LAMi_def, LAMi_termP,
             term_ABS_pseudo11, gterm_11, term_REP_11]);

val tpm_APPEND = store_thm(
  "ltpm_APPEND",
  ``ltpm (p1 ++ p2) t = ltpm p1 (ltpm p2 t)``,
  METIS_TAC [tpm_is_perm, is_perm_def]);

val term_CASES = save_thm(
  tyname ^ "_CASES",
  hd (Prim_rec.prove_cases_thm simple_induction))

(* alpha-convertibility *)
val ltpm_ALPHA = store_thm(
  "ltpm_ALPHA",
  ``~(v IN FV t) ==> (LAM u t = LAM v (ltpm [(v,u)] t))``,
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, tpm_flip_args]);
val ltpm_ALPHAi = store_thm(
  "ltpm_ALPHAi",
  ``~(v IN FV t) ==> (LAMi n u t M = LAMi n v (ltpm [(v,u)] t) M)``,
  SRW_TAC [boolSimps.CONJ_ss][LAMi_eq_thm, tpm_flip_args]);

val tpm_apart = store_thm(
  "ltpm_apart",
  ``!t. x IN FV t /\ y NOTIN FV t ==> ~(ltpm [(x,y)] t = t)``,
  srw_tac [][supp_apart])

val tpm_COND = prove(
  ``ltpm pi (if P then x else y) = if P then ltpm pi x else ltpm pi y``,
  srw_tac [][]);

val reordering = prove(
  ``(?(f:lterm -> (string # lterm) -> lterm). P f) <=>
    (?f. P (\M (v,N). f N v M))``,
  EQ_TAC THEN STRIP_TAC THENL [
    Q.EXISTS_TAC `λN x M. f M (x,N)` THEN SRW_TAC [][] THEN
    CONV_TAC (REDEPTH_CONV pairLib.PAIRED_ETA_CONV) THEN
    SRW_TAC [ETA_ss][],
    Q.EXISTS_TAC `λM (x,N). f N x M` THEN SRW_TAC [][]
  ]);

val subst_exists =
    parameter_tm_recursion
        |> INST_TYPE [alpha |-> ``:lterm``, ``:ρ`` |-> ``:string # lterm``]
        |> Q.INST [`A` |-> `{}`, `apm` |-> `ltpm`,
             `ppm` |-> `pairpm lswapstr ltpm`,
             `vr` |-> `\s (x,N). if s = x then N else VAR s`,
             `ap` |-> `\r1 r2 t1 t2 p. APP (r1 p) (r2 p)`,
             `lm` |-> `\r v t p. LAM v (r p)`,
             `li` |-> `\r1 r2 n v t1 t2 p. LAMi n v (r1 p) (r2 p)`]
        |> SIMP_RULE (srw_ss()) [tpm_COND, basic_swapTheory.swapstr_eq_left,
                                 tpm_fresh, fnpm_def, supp_fresh,
                                 is_perm_sing_inv, pairTheory.FORALL_PROD,
                                 reordering]
        |> elim_unnecessary_atoms {finite_fv = FINITE_FV} []
        |> prove_alpha_fcbhyp {ppm = ``pairpm lswapstr ltpm``,
                               alphas = [ltpm_ALPHA, ltpm_ALPHAi],
                               rwts = []}
        |> CONV_RULE (DEPTH_CONV
                      (rename_vars [("p_1", "u"), ("p_2", "N")]))

val SUB_DEF = new_specification("lSUB_DEF", ["SUB"], subst_exists)

val _ = add_rule {term_name = "SUB", fixity = Closefix,
                  pp_elements = [TOK "[", TM, TOK "/", TM, TOK "]"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2))};

val fresh_ltpm_subst = store_thm(
  "fresh_ltpm_subst",
  ``!t. ~(u IN FV t) ==> (ltpm [(u,v)] t = [VAR u/v] t)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_DEF]);

val l14a = Store_thm(
  "l14a",
  ``!t : lterm. [VAR v/v] t = t``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `{v}` THEN
  SRW_TAC [][SUB_DEF]);

val l14b = store_thm(
  "l14b",
  ``!t:lterm. ~(v IN FV t) ==> ([u/v]t = t)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `v INSERT FV u` THEN
  SRW_TAC [][SUB_DEF]);

val NOT_IN_FV_SUB_I = store_thm(
  "NOT_IN_FV_SUB_I",
  ``∀N u v M:lterm. v ∉ FV N ∧ v ≠ u ∧ v ∉ FV M ==> v ∉ FV ([N/u]M)``,
  NTAC 3 gen_tac >> ho_match_mp_tac lterm_bvc_induction >>
  qexists_tac `FV N ∪ {u;v}` >> srw_tac [][SUB_DEF]);

val lSUB_THM = Store_thm(
  "lSUB_THM",
  ``([N/x] (VAR x) = N) /\ (~(x = y) ==> ([N/x] (VAR y) = VAR y)) /\
    ([N/x] (M @@ P) = [N/x] M @@ [N/x] P) /\
    (~(v IN FV N) /\ ~(v = x) ==> ([N/x] (LAM v M) = LAM v ([N/x] M))) /\
    (~(v IN FV N) /\ ~(v = x) ==>
        ([N/x] (LAMi n v M P) = LAMi n v ([N/x]M) ([N/x]P)))``,
  SRW_TAC [][SUB_DEF]);
val lSUB_VAR = store_thm(
  "lSUB_VAR",
  ``[N/x] (VAR s : lterm) = if s = x then N else VAR s``,
  SRW_TAC [][SUB_DEF]);

val l15a = store_thm(
  "l15a",
  ``!t:lterm. ~(v IN FV t) ==> ([u/v] ([VAR v/x] t) = [u/x] t)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `{x;v} UNION FV u` THEN
  SRW_TAC [][lSUB_VAR]);

val ltm_recursion_nosideset = save_thm(
  "ltm_recursion_nosideset",
  tm_recursion |> Q.INST [`A` |-> `{}`] |> REWRITE_RULE [NOT_IN_EMPTY, FINITE_EMPTY])

val term_info_string =
    "local\n\
    \fun k |-> v = {redex = k, residue = v}\n\
    \val term_info = \n\
    \   {nullfv = ``labelledTerms$LAM \"\" (VAR \"\")``,\n\
    \    pm_rewrites = [],\n\
    \    pm_constant = ``labelledTerms$ltpm``,\n\
    \    fv_rewrites = [],\n\
    \    fv_constant = ``nomset$supp labelledTerms$ltpm``,\n\
    \    recursion_thm = SOME ltm_recursion_nosideset,\n\
    \    binders = [(``labelledTerms$LAM``, 0, ltpm_ALPHA),\n\
    \               (``labelledTerms$LAMi``, 1, ltpm_ALPHAi)]}\n\
    \val _ = binderLib.type_db :=\n\
    \          Binarymap.insert(!binderLib.type_db, \n\
    \                           {Thy = \"labelledTerms\", Name=\"lterm\"},\n\
    \                           binderLib.NTI term_info)\n\
    \in end;\n"

val _ = adjoin_to_theory
        { sig_ps = NONE,
          struct_ps =
          SOME (fn pps => PP.add_string pps term_info_string)}




val _ = export_theory()

