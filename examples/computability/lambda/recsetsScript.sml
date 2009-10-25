open HolKernel Parse bossLib boolLib

val _ = new_theory "recsets"

open recfunsTheory reductionEval
open binderLib
open stepsTheory

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val recursive_def = Define`
  recursive s = ∃M. ∀e. Phi M e = SOME (if e ∈ s then 1 else 0)
`;

val empty_recursive = Store_thm(
  "empty_recursive",
  ``recursive {}``,
  SRW_TAC [][recursive_def, Phi_def] THEN
  Q.EXISTS_TAC `dBnum (fromTerm (LAM v (church 0)))` THEN
  SIMP_TAC (bsrw_ss()) [normal_orderTheory.bnf_bnf_of]);

val univ_recursive = Store_thm(
  "univ_recursive",
  ``recursive UNIV``,
  SRW_TAC [][recursive_def, Phi_def] THEN
  Q.EXISTS_TAC `dBnum (fromTerm (LAM v (church 1)))` THEN
  SIMP_TAC (bsrw_ss()) [normal_orderTheory.bnf_bnf_of]);

val union_recursive_I = Store_thm(
  "union_recursive_I",
  ``recursive s₁ ∧ recursive s₂ ⇒ recursive (s₁ ∪ s₂)``,
  SRW_TAC [][recursive_def] THEN
  SIMP_TAC (srw_ss()) [Phi_def] THEN
  Q.EXISTS_TAC
    `dBnum (fromTerm
      (LAM z (cor @@ (ceqnat @@ (church 1)
                             @@ (UM @@ (cnpair @@ church M @@ VAR z)))
                  @@ (ceqnat @@ (church 1)
                             @@ (UM @@ (cnpair @@ church M' @@ VAR z)))
                  @@ church 1
                  @@ church 0)))` THEN
  Q.X_GEN_TAC `n` THEN
  REPEAT (FIRST_X_ASSUM (Q.SPEC_THEN `n` STRIP_ASSUME_TAC)) THEN
  IMP_RES_TAC PhiSOME_UM_I THEN
  ASM_SIMP_TAC (bsrw_ss()) [churchnumTheory.cnpair_behaviour,
                            churchnumTheory.ceqnat_behaviour] THEN
  Cases_on `n ∈ s₁` THEN Cases_on `n ∈ s₂` THEN
  ASM_SIMP_TAC (bsrw_ss()) [churchboolTheory.cor_behaviour,
                            churchboolTheory.cB_behaviour,
                            normal_orderTheory.bnf_bnf_of]);

val inter_recursive_I = Store_thm(
  "inter_recursive_I",
  ``recursive s₁ ∧ recursive s₂ ⇒ recursive (s₁ ∩ s₂)``,
  SRW_TAC [][recursive_def] THEN
  SIMP_TAC (srw_ss()) [Phi_def] THEN
  Q.EXISTS_TAC `
    dBnum (fromTerm
      (LAM z (cmult @@ (UM @@ (cnpair @@ church M @@ VAR z))
                    @@ (UM @@ (cnpair @@ church M' @@ VAR z)))))` THEN
  Q.X_GEN_TAC `n` THEN
  REPEAT (FIRST_X_ASSUM (Q.SPEC_THEN `n` STRIP_ASSUME_TAC)) THEN
  IMP_RES_TAC PhiSOME_UM_I THEN
  ASM_SIMP_TAC (bsrw_ss()) [churchnumTheory.cnpair_behaviour,
                            churchnumTheory.cmult_behaviour,
                            normal_orderTheory.bnf_bnf_of] THEN
  Cases_on `n ∈ s₁` THEN SRW_TAC [][]);

val compl_recursive_I = store_thm(
  "compl_recursive_I",
  ``recursive s ⇒ recursive (COMPL s)``,
  SRW_TAC [][recursive_def] THEN
  SIMP_TAC (srw_ss()) [Phi_def] THEN
  Q.EXISTS_TAC `
    dBnum (fromTerm
      (LAM z (cminus @@ (church 1)
                     @@ (UM @@ (cnpair @@ church M @@ VAR z)))))` THEN
  Q.X_GEN_TAC `n` THEN
  POP_ASSUM (Q.SPEC_THEN `n` STRIP_ASSUME_TAC) THEN
  IMP_RES_TAC PhiSOME_UM_I THEN
  ASM_SIMP_TAC (bsrw_ss()) [churchnumTheory.cnpair_behaviour,
                            churchnumTheory.cminus_behaviour,
                            normal_orderTheory.bnf_bnf_of] THEN
  Cases_on `n ∈ s` THEN SRW_TAC [][]);

val compl_recursive = Store_thm(
  "compl_recursive",
  ``recursive (COMPL s) ⇔ recursive s``,
  METIS_TAC [pred_setTheory.COMPL_COMPL, compl_recursive_I]);

val finite_recursive = Store_thm(
  "finite_recursive",
  ``∀s. FINITE s ==> recursive s``,
  HO_MATCH_MP_TAC pred_setTheory.FINITE_INDUCT THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [recursive_def] THEN
  SIMP_TAC (srw_ss()) [Phi_def] THEN
  Q.EXISTS_TAC `
    dBnum (fromTerm
      (LAM z (cor @@ (ceqnat @@ VAR z @@ church e)
                  @@ (ceqnat @@ church 1
                             @@ (UM @@ (cnpair @@ church M @@ VAR z)))
                  @@ church 1
                  @@ church 0)))` THEN
  Q.X_GEN_TAC `n` THEN FIRST_X_ASSUM (Q.SPEC_THEN `n` STRIP_ASSUME_TAC) THEN
  IMP_RES_TAC PhiSOME_UM_I THEN
  ASM_SIMP_TAC (bsrw_ss()) [churchnumTheory.cnpair_behaviour,
                            churchnumTheory.ceqnat_behaviour,
                            churchboolTheory.cor_behaviour] THEN
  Cases_on `n = e` THEN
  ASM_SIMP_TAC (bsrw_ss()) [churchboolTheory.cB_behaviour,
                            normal_orderTheory.bnf_bnf_of] THEN
  Cases_on `n ∈ s` THEN
  ASM_SIMP_TAC (bsrw_ss()) [churchboolTheory.cB_behaviour,
                            normal_orderTheory.bnf_bnf_of]);

(* an r.e. set is one that can be enumerated.  In this world, I take enumerable
   to mean there exists a function that returns values at successive indices.
*)
val re_def = Define`
  re s = ∃Mi. ∀e. e ∈ s ⇔ ∃j. Phi Mi j = SOME e
`;

(* if a set s is r.e., then there is a machine that terminates on only those
   elements of the set (and fails to terminate on non-members)

   Say the machine we have that enumerates s is Mi.  Then we want one that
   will correctly terminate on element e of s.
   For increasing n, construct the list of n elements corresponding to
   evaluating [Mi 0, Mi 1, Mi 2, ... Mi n] for n steps.  For all the bnfs in
   this list, see if one of them is equal to e.  If so, terminate.
*)
val enum2semibody_def = Define`
  enum2semibody Mi e loop n j =
    LAM loop (LAM n
      (cmem @@ e
            @@ (cmap @@ cforce_num
                     @@ (cfilter
                           @@ cbnf
                           @@ (ctabulate
                                 @@ (csuc @@ VAR n)
                                 @@ (LAM j
                                       (csteps
                                          @@ VAR n
                                          @@ (cdAPP
                                                @@ (cnumdB @@ church Mi)
                                                @@ (cchurch @@ VAR j)))))))
            @@ church 0
            @@ (VAR loop @@ (csuc @@ VAR n))))
`;

val enum2semi_def = Define`
  enum2semi Mi e =
    let loop = NEW (FV e) in
    let n = NEW ({loop} ∪ FV e) in
    let j = NEW {n}
    in
       enum2semibody Mi e loop n j
`;

val FV_enum2semi = prove(
  ``FV (enum2semi n t) = FV t``,
  SRW_TAC [][enum2semi_def, LET_THM, pred_setTheory.EXTENSION,
             enum2semibody_def] THEN
  binderLib.NEW_ELIM_TAC THEN REPEAT GEN_TAC THEN
  binderLib.NEW_ELIM_TAC THEN SRW_TAC [][] THEN
  METIS_TAC []);

val enum2semi_fresh = prove(
  ``loop ∉ FV e ∧ n ≠ loop ∧ n ∉ FV e ∧ j ≠ n ⇒
     (enum2semi Mi e = enum2semibody Mi e loop n j)``,
  SRW_TAC [][enum2semi_def, LET_THM] THEN
  binderLib.NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  binderLib.NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  binderLib.NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  SRW_TAC [][enum2semibody_def, termTheory.LAM_eq_thm,
             termTheory.tpm_fresh] THEN
  Cases_on `loop = v` THEN SRW_TAC [][] THEN1
    (SRW_TAC [][basic_swapTheory.swapstr_def] THEN METIS_TAC []) THEN
  Cases_on `v = n` THEN SRW_TAC [][] THEN
  Cases_on `loop = n` THEN SRW_TAC [][] THENL [
    Cases_on `loop = j` THEN SRW_TAC [][] THEN
    SRW_TAC [][basic_swapTheory.swapstr_def, termTheory.tpm_fresh] THEN
    METIS_TAC [],

    Cases_on `loop = j` THEN SRW_TAC [][] THEN1
      (SRW_TAC [][basic_swapTheory.swapstr_def, termTheory.tpm_fresh] THEN
       METIS_TAC []) THEN
    Cases_on `v = j` THEN SRW_TAC [][] THEN
    SRW_TAC [][basic_swapTheory.swapstr_def, termTheory.tpm_fresh] THEN
    METIS_TAC []
  ]);

(* val enum2semi_eqn = brackabs.brackabs_equiv [] (SPEC_ALL enum2semi_def) *)

val enum2semi_SUB = store_thm(
  "enum2semi_SUB",
  ``[N/v] (enum2semi n t) = enum2semi n ([N/v]t)``,
  Q_TAC (NEW_TAC "loop") `FV N ∪ {v} ∪ FV t` THEN
  Q_TAC (NEW_TAC "m") `FV N ∪ {v; loop} ∪ FV t` THEN
  Q_TAC (NEW_TAC "j") `FV N ∪ {v;m}` THEN
  `enum2semi n t = enum2semibody n t loop m j`
     by METIS_TAC [enum2semi_fresh] THEN
  `enum2semi n ([N/v]t) = enum2semibody n ([N/v]t) loop m j`
     by (MATCH_MP_TAC enum2semi_fresh THEN
         SRW_TAC [][chap2Theory.NOT_IN_FV_SUB]) THEN
  SRW_TAC [][enum2semibody_def, termTheory.lemma14b]);

(* val re_semirecursive1 = prove(
  ``re s ⇒ ∃N. ∀e. e ∈ s ⇔ ∃m. Phi N e = SOME m``,
  SRW_TAC [][re_def] THEN
  Q.EXISTS_TAC
    `dBnum (fromTerm
              (LAM "e" (chap2$Y @@ enum2semi Mi (VAR "e") @@ church 0)))` THEN
  SRW_TAC [][Phi_def, EQ_IMP_THM] THENL [
    SIMP_TAC (bsrw_ss()) [churchDBTheory.cnumdB_behaviour,
                          Once chap2Theory.lameq_Y]

*)
(*
val recursive_re = store_thm(
  "recursive_re",
  ``recursive s ⇒ re s``,
  SRW_TAC [][recursive_def, re_def] THEN
  `dBnum (fromTerm

*)




val _ = export_theory ()
