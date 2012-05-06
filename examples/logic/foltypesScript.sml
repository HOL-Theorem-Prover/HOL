open HolKernel boolLib Parse bossLib

open binderLib
open nomdatatype
open nomsetTheory
open generic_termsTheory
open lcsymtacs

fun Save_thm (nm, th) = save_thm(nm,th) before export_rewrites [nm]
fun Store_thm(nm,t,tac) = store_thm(nm,t,tac) before export_rewrites [nm]

val _ = new_theory "foltypes"

val _ = set_fixity "=" (Infix(NONASSOC, 450))

val tyname = "foterm"

val _ = Hol_datatype `
  ftm_discriminator = ftmFN of string | ftmRN of string | ftmF | ftmIMP |
                      ftmALL
`;

val [gvar,glam] = genind_rules |> SPEC_ALL |> CONJUNCTS

val vp = ``(λn u:unit. n = 0)``
val lp = ``
  (λn d:ftm_discriminator tns uns.
     n = 0 ∧ (∃s. d = ftmFN s) ∧ (∀i. MEM i uns ⇒ i = 0) ∧ tns = [] ∨
     n = 1 ∧ (∃s. d = ftmRN s) ∧ (∀i. MEM i uns ⇒ i = 0) ∧ tns = [] ∨
     n = 1 ∧ d = ftmF ∧ uns = [] ∧ tns = [] ∨
     n = 1 ∧ d = ftmIMP ∧ uns = [1;1] ∧ tns = [] ∨
     n = 1 ∧ d = ftmALL ∧ uns = [] ∧ tns = [1])
``

val {term_ABS_pseudo11, term_REP_11, genind_term_REP, genind_exists,
     termP, absrep_id = term_absrep_id,
     repabs_pseudo_id = term_repabs_pseudo_id,
     term_REP_t, term_ABS_t,
     newty = term_ty, ...} =
    new_type_step1 tyname 0 {vp=vp, lp = lp}

val VAR_t = mk_var("VAR", ``:string -> ^term_ty``)
val VAR_def = new_definition(
  "VAR_def",
  ``^VAR_t s = ^term_ABS_t (GVAR s ())``);
val VAR_termP = prove(
  mk_comb(termP, VAR_def |> SPEC_ALL |> concl |> rhs |> rand),
  srw_tac[][genind_rules]);
val VAR_t = defined_const VAR_def

val FN_t = mk_var("FN", ``:string -> ^term_ty list -> ^term_ty``)
val FN_def = new_definition(
  "FN_def",
  ``^FN_t s args =
    ^term_ABS_t (GLAM ARB (ftmFN s) [] (MAP ^term_REP_t args))``);
val FN_termP = prove(
  ``^termP (GLAM x (ftmFN s) [] (MAP ^term_REP_t args))``,
  match_mp_tac glam >> srw_tac [][genind_term_REP] >>
  qexists_tac `GENLIST (λn. 0) (LENGTH args)` >>
  simp[listTheory.MEM_GENLIST,
       listTheory.LIST_REL_EL_EQN, listTheory.EL_MAP, genind_term_REP])
val FN_t = defined_const FN_def

val FN_def' = prove(
  ``^term_ABS_t (GLAM v (ftmFN s) [] (MAP ^term_REP_t args)) = ^FN_t s args``,
  srw_tac[][FN_def, GLAM_NIL_EQ, term_ABS_pseudo11, FN_termP]);

val tm_cons_info = [{con_termP = VAR_termP, con_def = VAR_def},
                    {con_termP = FN_termP, con_def = SYM FN_def'}]
val tpm_name_pfx = "t"

val {tpm_thm = tpm_thm0, term_REP_tpm, t_pmact_t, tpm_t} =
    define_permutation { name_pfx = "t", name = tyname,
                         term_REP_t = term_REP_t,
                         term_ABS_t = term_ABS_t, absrep_id = term_absrep_id,
                         repabs_pseudo_id = term_repabs_pseudo_id,
                         cons_info = tm_cons_info, newty = term_ty,
                         genind_term_REP = genind_term_REP}

val tpm_thm = save_thm(
  "tpm_thm",
  tpm_thm0 |> SIMP_RULE bool_ss [listpm_MAP, listTheory.MAP_MAP_o,
                                 combinTheory.o_DEF, SYM term_REP_tpm]
           |> REWRITE_RULE [GSYM combinTheory.o_DEF,
                            GSYM listTheory.MAP_MAP_o]
           |> REWRITE_RULE [FN_def']);

val forms_exist = prove(
  ``∃x. genind ^vp ^lp 1 x``,
  qexists_tac `GLAM ARB (ftmRN s) [] []` >>
  match_mp_tac glam >> simp[] >> qexists_tac `[]` >> simp[]);

val {absrep_id = form_absrep_id, newty = form_ty,
     repabs_pseudo_id = form_repabs_pseudo_id, termP = formP, termP_exists,
     termP_term_REP = formP_form_REP,
     term_ABS_t = form_ABS_t, term_ABS_pseudo11 = form_ABS_pseudo11,
     term_REP_t = form_REP_t, term_REP_11} =
    newtypeTools.rich_new_type ("form", forms_exist)

val ALL_t = mk_var("ALL", ``:string -> ^form_ty -> ^form_ty``)
val ALL_def = new_definition(
  "ALL_def",
  ``^ALL_t s body =
    ^form_ABS_t (GLAM s ftmALL [^form_REP_t body] [])``);
val ALL_formP = prove(
  mk_comb(formP, ALL_def |> SPEC_ALL |> concl |> rhs |> rand),
  match_mp_tac glam >> simp[formP_form_REP]);
val ALL_t = defined_const ALL_def

val REL_t = mk_var("REL", ``:string -> ^term_ty list -> ^form_ty``)
val REL_def = new_definition(
  "REL_def",
  ``^REL_t s args =
    ^form_ABS_t (GLAM ARB (ftmRN s) [] (MAP ^term_REP_t args))``);
val REL_formP = prove(
  ``^formP (GLAM v (ftmRN s) [] (MAP ^term_REP_t args))``,
  match_mp_tac glam >> simp[genind_term_REP] >>
  qexists_tac `GENLIST (\n. 0) (LENGTH args)` >>
  simp[listTheory.MEM_GENLIST,
       listTheory.LIST_REL_EL_EQN, listTheory.EL_MAP, genind_term_REP])
val REL_t = defined_const REL_def
val REL_def' = prove(
  ``^form_ABS_t (GLAM v (ftmRN s) [] (MAP ^term_REP_t args)) = ^REL_t s args``,
  srw_tac[][REL_def, GLAM_NIL_EQ, form_ABS_pseudo11, REL_formP]);

val FALSE_t = mk_var("FALSE", ``:^form_ty``)
val FALSE_def = new_definition(
  "FALSE_def",
  ``^FALSE_t = ^form_ABS_t (GLAM ARB ftmF [] [])``);
val FALSE_formP = prove(
  ``^formP (GLAM v ftmF [] [])``,
  match_mp_tac glam >> simp[]);
val FALSE_t = defined_const FALSE_def
val FALSE_def' = prove(
  ``^form_ABS_t (GLAM v ftmF [] []) = ^FALSE_t``,
  srw_tac[][FALSE_def, GLAM_NIL_EQ, form_ABS_pseudo11, FALSE_formP])

val IMP_t = mk_var("IMP", ``:^form_ty -> ^form_ty -> ^form_ty``)
val IMP_def = new_definition("IMP_def",
  ``^IMP_t f1 f2 =
    ^form_ABS_t (GLAM ARB ftmIMP [] [^form_REP_t f1; ^form_REP_t f2])``);
val IMP_formP = prove(
  ``^formP (GLAM v ftmIMP [] [^form_REP_t f1; ^form_REP_t f2])``,
  match_mp_tac glam >> simp[formP_form_REP]);
val IMP_t = defined_const IMP_def
val IMP_def' = prove(
  ``^form_ABS_t (GLAM v ftmIMP [] [^form_REP_t f1; ^form_REP_t f2]) =
    ^IMP_t f1 f2``,
  rw[IMP_def, GLAM_NIL_EQ, form_ABS_pseudo11, IMP_formP]);

val fm_cons_info = [{con_termP = REL_formP, con_def = GSYM REL_def'},
                    {con_termP = ALL_formP, con_def = ALL_def},
                    {con_termP = FALSE_formP, con_def = GSYM FALSE_def'},
                    {con_termP = IMP_formP, con_def = GSYM IMP_def'}]
val tpm_name_pfx = "f"

val {tpm_thm = fpm_thm0, term_REP_tpm = form_REP_fpm, t_pmact_t = f_pmact_t,
     tpm_t = fpm_t} =
    define_permutation { name_pfx = "f", name = "form",
                         term_REP_t = form_REP_t,
                         term_ABS_t = form_ABS_t, absrep_id = form_absrep_id,
                         repabs_pseudo_id = form_repabs_pseudo_id,
                         cons_info = fm_cons_info, newty = form_ty,
                         genind_term_REP = formP_form_REP}

val fpm_thm = save_thm(
  "fpm_thm",
  fpm_thm0 |> SIMP_RULE bool_ss [listpm_MAP, listTheory.MAP_MAP_o,
                                 combinTheory.o_DEF, SYM term_REP_tpm]
           |> REWRITE_RULE [GSYM combinTheory.o_DEF,
                            GSYM listTheory.MAP_MAP_o]
           |> REWRITE_RULE [REL_def'])

(* support *)
val term_REP_eqv = prove(
   ``support (fn_pmact ^t_pmact_t gt_pmact) ^term_REP_t {}`` ,
   srw_tac [][support_def, fnpm_def, FUN_EQ_THM, term_REP_tpm, pmact_sing_inv]);

val supp_term_REP = prove(
  ``supp (fn_pmact ^t_pmact_t gt_pmact) ^term_REP_t = {}``,
  REWRITE_TAC [GSYM pred_setTheory.SUBSET_EMPTY] >>
  MATCH_MP_TAC (GEN_ALL supp_smallest) >>
  srw_tac [][term_REP_eqv])

val tpm_def' =
    term_REP_tpm |> AP_TERM term_ABS_t |> PURE_REWRITE_RULE [term_absrep_id]

val t = mk_var("t", term_ty)
val supptpm_support = prove(
  ``support ^t_pmact_t ^t (supp gt_pmact (^term_REP_t ^t))``,
  srw_tac [][support_def, tpm_def', supp_fresh, term_absrep_id]);

val supptpm_apart = prove(
  ``x ∈ supp gt_pmact (^term_REP_t ^t) ∧ y ∉ supp gt_pmact (^term_REP_t ^t) ⇒
    ^tpm_t [(x,y)] ^t ≠ ^t``,
  srw_tac [][tpm_def']>>
  DISCH_THEN (MP_TAC o AP_TERM term_REP_t) >>
  srw_tac [][term_repabs_pseudo_id, genind_gtpm_eqn, genind_term_REP,
             supp_apart]);

val supp_tpm = prove(
  ``supp ^t_pmact_t ^t = supp gt_pmact (^term_REP_t ^t)``,
  match_mp_tac (GEN_ALL supp_unique_apart) >>
  srw_tac [][supptpm_support, supptpm_apart, FINITE_GFV])

val supp_tpml = prove(
  ``supp (list_pmact ^t_pmact_t) ts = GFVl (MAP foterm_REP ts)``,
  Induct_on `ts` >> simp[supp_tpm]);

val _ = overload_on ("tFV", ``supp ^t_pmact_t``)
val _ = overload_on ("tFVl", ``supp (list_pmact ^t_pmact_t)``)

val FINITE_tFV = store_thm(
  "FINITE_tFV",
  ``FINITE (tFV t)``,
  srw_tac [][supp_tpm, FINITE_GFV]);
val _ = export_rewrites ["FINITE_tFV"]

fun supp_clause repabs_pseudo_id {con_termP, con_def} = let
  open pred_setTheory
  val t = mk_comb(``supp ^t_pmact_t``, lhand (concl (SPEC_ALL con_def)))
in
  t |> REWRITE_CONV [supp_tpm, con_def, MATCH_MP repabs_pseudo_id con_termP,
                     GFV_thm]
    |> REWRITE_RULE [supp_listpm, EMPTY_DELETE, UNION_EMPTY]
    |> REWRITE_RULE [GSYM supp_tpm, GSYM supp_tpml]
    |> GEN_ALL
end

val tFV_thm = Save_thm(
  "tFV_thm",
  LIST_CONJ (map (supp_clause term_repabs_pseudo_id) tm_cons_info))

val form_REP_eqv = prove(
   ``support (fn_pmact ^f_pmact_t gt_pmact) ^form_REP_t {}`` ,
   srw_tac [][support_def, fnpm_def, FUN_EQ_THM, form_REP_fpm, pmact_sing_inv]);

val supp_form_REP = prove(
  ``supp (fn_pmact ^f_pmact_t gt_pmact) ^form_REP_t = {}``,
  REWRITE_TAC [GSYM pred_setTheory.SUBSET_EMPTY] >>
  MATCH_MP_TAC (GEN_ALL supp_smallest) >>
  srw_tac [][form_REP_eqv])

val fpm_def' =
    form_REP_fpm |> AP_TERM form_ABS_t |> PURE_REWRITE_RULE [form_absrep_id]

val t = mk_var("f", form_ty)
val supptpm_support = prove(
  ``support ^f_pmact_t ^t (supp gt_pmact (^form_REP_t ^t))``,
  srw_tac [][support_def, fpm_def', supp_fresh, form_absrep_id]);

val supptpm_apart = prove(
  ``x ∈ supp gt_pmact (^form_REP_t ^t) ∧ y ∉ supp gt_pmact (^form_REP_t ^t) ⇒
    ^fpm_t [(x,y)] ^t ≠ ^t``,
  srw_tac [][fpm_def']>>
  DISCH_THEN (MP_TAC o AP_TERM form_REP_t) >>
  srw_tac [][form_repabs_pseudo_id, genind_gtpm_eqn, formP_form_REP,
             supp_apart]);

val supp_tpm = prove(
  ``supp ^f_pmact_t ^t = supp gt_pmact (^form_REP_t ^t)``,
  match_mp_tac (GEN_ALL supp_unique_apart) >>
  srw_tac [][supptpm_support, supptpm_apart, FINITE_GFV])

val _ = overload_on ("fFV", ``supp ^f_pmact_t``)

val FINITE_fFV = store_thm(
  "FINITE_fFV",
  ``FINITE (fFV f)``,
  srw_tac [][supp_tpm, FINITE_GFV]);
val _ = export_rewrites ["FINITE_fFV"]

fun supp_clause repabs_pseudo_id {con_termP, con_def} = let
  open pred_setTheory
  val t = mk_comb(``supp ^f_pmact_t``, lhand (concl (SPEC_ALL con_def)))
in
  t |> REWRITE_CONV [supp_tpm, con_def, MATCH_MP repabs_pseudo_id con_termP,
                     GFV_thm]
    |> REWRITE_RULE [supp_listpm, EMPTY_DELETE, UNION_EMPTY]
    |> REWRITE_RULE [GSYM supp_tpm, GSYM supp_tpml]
    |> GEN_ALL
end

val fFV_thm = Save_thm(
  "fFV_thm",
  LIST_CONJ (map (supp_clause form_repabs_pseudo_id) fm_cons_info))

val LIST_REL_CONS1 = listTheory.LIST_REL_CONS1
val LIST_REL_NIL = listTheory.LIST_REL_NIL

val term_ind0 =
    bvc_genind
        |> INST_TYPE [alpha |-> ``:ftm_discriminator``, beta |-> ``:unit``]
        |> Q.INST [`vp` |-> `^vp`, `lp` |-> `^lp`]
        |> Q.SPEC `λn t0 x. (n = 0) ⇒ Q t0 x`
        |> Q.INST [`Q` |-> `λt. P (foterm_ABS t)`]
        |> SPEC_ALL
        |> UNDISCH_ALL |> SIMP_RULE std_ss []
        |> SPECL [``0n``, ``foterm_REP ft``]
        |> SIMP_RULE std_ss [genind_term_REP, term_absrep_id]
        |> Q.GEN `ft` |> DISCH_ALL
        |> SIMP_RULE std_ss [LEFT_AND_OVER_OR, DISJ_IMP_THM, LIST_REL_CONS1,
                             LIST_REL_NIL,
                             RIGHT_AND_OVER_OR, FORALL_AND_THM, GSYM VAR_def,
                             oneTheory.FORALL_ONE]
        |> Q.INST [`P` |-> `λt x. Q t`, `fv` |-> `λx. {}`]
        |> SIMP_RULE (srw_ss()) [] |> Q.GEN `Q`

val foterm_ind = store_thm(
  "foterm_ind",
  ``!P.
      (∀s. P (VAR s)) ∧
      (∀s ts. (∀t. MEM t ts ⇒ P t) ⇒ P (FN s ts)) ⇒
      ∀ft. P ft``,
  rpt gen_tac >> strip_tac >> match_mp_tac term_ind0 >> simp[] >>
  rw[listTheory.LIST_REL_EL_EQN] >>
  `∀i. i < LENGTH uns ⇒ EL i uns = 0` by metis_tac [listTheory.MEM_EL] >>
  fs[] >>
  `∃ts. us = MAP foterm_REP ts`
     by (qexists_tac `MAP foterm_ABS us` >>
         simp[listTheory.MAP_MAP_o] >>
         match_mp_tac listTheory.LIST_EQ >> simp[listTheory.EL_MAP] >>
         qx_gen_tac `i` >> rw[] >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
         match_mp_tac term_repabs_pseudo_id >> metis_tac[]) >>
  simp[FN_def'] >> first_x_assum match_mp_tac >>
  rw[] >> qpat_assum `∀n. n < LENGTH uns ⇒ PP ∧ QQ` mp_tac >>
  simp[listTheory.EL_MAP, term_absrep_id] >>
  `∃n. n < LENGTH ts ∧ t = EL n ts` by metis_tac[listTheory.MEM_EL] >>
  simp[])

val _ = export_theory()
