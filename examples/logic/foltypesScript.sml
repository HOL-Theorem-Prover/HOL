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
     termP, absrep_id, repabs_pseudo_id, term_REP_t, term_ABS_t,
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
                         term_ABS_t = term_ABS_t, absrep_id = absrep_id,
                         repabs_pseudo_id = repabs_pseudo_id,
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

val {absrep_id, newty = form_ty,
     repabs_pseudo_id, termP = formP, termP_exists,
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
                         term_ABS_t = form_ABS_t, absrep_id = absrep_id,
                         repabs_pseudo_id = repabs_pseudo_id,
                         cons_info = fm_cons_info, newty = form_ty,
                         genind_term_REP = formP_form_REP}

val fpm_thm = save_thm(
  "fpm_thm",
  fpm_thm0 |> SIMP_RULE bool_ss [listpm_MAP, listTheory.MAP_MAP_o,
                                 combinTheory.o_DEF, SYM term_REP_tpm]
           |> REWRITE_RULE [GSYM combinTheory.o_DEF,
                            GSYM listTheory.MAP_MAP_o]
           |> REWRITE_RULE [REL_def'])



val _ = export_theory()
