open HolKernel boolLib bossLib Parse
open termTheory nomsetTheory
open binderLib

val _ = new_theory "precn" (* "parameter recursion" *)

open lcsymtacs
val lemma1 = prove(
  ``tpm [(x,y)] (if s1:string = s2 then t1 else t2) =
    if s1 = s2 then tpm [(x,y)] t1 else tpm [(x,y)] t2``,
  SRW_TAC [][]);

val lmf0 = ``λy'. fnpm tpm tpm [(y,y')] r (x2 @@ e)``

val lmf_support = prove(
  ``support (fnpm lswapstr tpm) ^lmf0
            (supp (fnpm tpm tpm) r ∪ FV x2 ∪ FV e ∪ {y})``,
  SRW_TAC [][support_def, fnpm_def, FUN_EQ_THM] >>
  `∀t. tpm [(x,y')] (r t) = r (tpm [(x,y')] t)`
     by (GEN_TAC >> Q_TAC SUFF_TAC `fnpm tpm tpm [(x,y')] r = r`
           THEN1 (DISCH_THEN
                      (fn th => SRW_TAC [][Once (SYM th), SimpLHS]) >>
                  srw_tac [][fnpm_def]) >>
         srw_tac [][supp_fresh]) >>
  srw_tac [][Once (GSYM tpm_sing_to_back)] >>
  srw_tac [][Once (GSYM tpm_sing_to_back)] >>
  srw_tac [][tpm_fresh] >>
  srw_tac [][Once (GSYM tpm_sing_to_back)] >>
  srw_tac [][tpm_fresh]);

val lmf_fcond = prove(
  ``y ∉ FV x2 ∪ FINITE (supp (fnpm tpm tpm) r) ==> fcond tpm ^lmf0``,
  srw_tac [][fcond_def] >>


val precn0 =
    tm_recursion
        |> SPEC_ALL
        |> Q.INST_TYPE [`:'a` |-> `:term -> term`]
        |> Q.INST [`vr` |-> `λs N. if s = u then N else VAR s`,
                   `ap` |-> `λr1 r2 t1 t2 N. r1 N @@ r2 N`,
                   `lm` |-> `λr y t N. fresh tpm
                                      (λy'. fnpm tpm tpm [(y,y')] r (x2 @@ N))`,
                   `A` |-> `u INSERT FV x2`,
                   `apm` |-> `fnpm tpm tpm`]
        |> SIMP_RULE (srw_ss()) [FUN_EQ_THM, fnpm_def, lemma1,
                                 basic_swapTheory.swapstr_eq_left]

fun provehyps (th, tac) = let
  val (h,c) = dest_imp (concl th)
  val hth = prove(h,tac)
in
  MATCH_MP th hth
end

fun gphyps th = set_goal([], #1 (dest_imp (concl th)))
(* gphyps precn0 *)


open pred_setTheory
val notinsupp_I = prove(
  ``∀A apm e x.
       is_perm apm ∧ FINITE A ∧ support apm x A ∧ e ∉ A ==> e ∉ supp apm x``,
  metis_tac [supp_smallest, SUBSET_DEF]);


val precn = provehyps(
  precn0,
  srw_tac [][] >| [
    qmatch_abbrev_tac `tpm [(x,y)] (fresh tpm f) = fresh tpm g` >>
    `support (fnpm tpm tpm) r (u INSERT FV x2 ∪ FV t)`
       by srw_tac [][support_def, supp_fresh] >>
    `∀a b. a ∉ FV x2 ∧ a ∉ FV t ∧ a ≠ u ∧
           b ∉ FV x2 ∧ b ∉ FV t ∧ b ≠ u ==>
           ∀t. tpm [(a,b)] (r t) = r (tpm [(a,b)] t)`
       by (srw_tac [][] >>
           `r = fnpm tpm tpm [(a,b)] r` by srw_tac [][supp_fresh] >>
           pop_assum (fn th => srw_tac [][Once th, SimpLHS]) >>
           srw_tac [][fnpm_def]) >>
    `support (fnpm lswapstr tpm) f ({u;v;x;y} ∪ FV t ∪ FV x2 ∪ FV x')`
       by (srw_tac [][support_def, FUN_EQ_THM, fnpm_def] >>
           qunabbrev_tac `f` >> srw_tac [][] >>
           srw_tac [][Once (GSYM tpm_sing_to_back), is_perm_injective] >>
           srw_tac [][Once (GSYM tpm_sing_to_back), SimpLHS] >>
           srw_tac [][tpm_fresh] >>
           srw_tac [][Once (GSYM tpm_sing_to_back), SimpLHS] >>
           srw_tac [][tpm_fresh]) >>
    `fcond tpm f`
      by (srw_tac [][fcond_def]
          >- (match_mp_tac (GEN_ALL support_FINITE_supp) >>
              qexists_tac `{u;v;x;y} ∪ FV t ∪ FV x2 ∪ FV x'` >>
              srw_tac [][]) >>
          Q_TAC (NEW_TAC "z") `{u;v;x;y} ∪ FV t ∪ FV x2 ∪ FV x'` >>
          qexists_tac `z` >> srw_tac [][]
          >- (match_mp_tac notinsupp_I >>
              qexists_tac `{u;v;x;y} ∪ FV t ∪ FV x2 ∪ FV x'` >>
              srw_tac [][]) >>x
          srw_tac [][Abbr`f`]





val _ = export_theory()


