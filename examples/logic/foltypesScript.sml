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
     n = 1 ∧ d = ftmIMP ∧ uns = [0;0] ∧ tns = [] ∨
     n = 1 ∧ d = ftmALL ∧ uns = [] ∧ tns = [1])
``

val {term_ABS_pseudo11, term_REP_11, genind_term_REP, genind_exists,
     termP, absrep_id, repabs_pseudo_id, term_REP_t, term_ABS_t, newty, ...} =
    new_type_step1 tyname 0 {vp=vp, lp = lp}

val VAR_t = mk_var("VAR", ``:string -> ^newty``)
val VAR_def = new_definition(
  "VAR_def",
  ``^VAR_t s = ^term_ABS_t (GVAR s ())``);
val VAR_termP = prove(
  mk_comb(termP, VAR_def |> SPEC_ALL |> concl |> rhs |> rand),
  srw_tac[][genind_rules]);
val VAR_t = defined_const VAR_def

val FN_t = mk_var("FN", ``:string -> ^newty list -> ^newty``)
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
                         cons_info = tm_cons_info, newty = newty,
                         genind_term_REP = genind_term_REP}

val tpm_thm = tpm_thm0
                  |> SIMP_RULE bool_ss [listpm_MAP, listTheory.MAP_MAP_o,
                                        combinTheory.o_DEF, SYM term_REP_tpm]
                  |> REWRITE_RULE [GSYM combinTheory.o_DEF,
                                   GSYM listTheory.MAP_MAP_o]
                  |> REWRITE_RULE [FN_def']

(* val {term_ABS_pseudo11 = form_ABS_pseudo11,
     term_REP_11 = form_REP_11,
     genind_term_REP = genind_form_REP,
     genind_exists,
     termP = formP,
     absrep_id = form_absrep_id,
     repabs_pseudo_id = form_repabs_pseudo_id,
     term_REP_t = form_REP_t, term_ABS_t = form_ABS_t, newty = formty, ...} =
    new_type_step1 "form" 1 {vp=vp, lp = lp} *)

val _ = export_theory()
