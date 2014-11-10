(*  This theory covers the semi-automatic proofs on primitive operations *)
(*     and simplification concepts needed to show the user lemma         *)
(*  Author: Oliver Schwarz                                               *)

open HolKernel boolLib bossLib Parse proofManagerLib;
open arm_coretypesTheory arm_seq_monadTheory arm_opsemTheory arm_stepTheory;
open MMUTheory MMU_SetupTheory inference_rulesTheory switching_lemma_helperTheory switching_lemmaTheory;
open tacticsLib ARM_proverLib ARM_prover_toolsLib;
open user_lemma_basicsTheory;
open wordsTheory wordsLib;

val _ =  new_theory("user_lemma_primitive_operations");

val _ = goalStack.chatting := !Globals.interactive
val _ = temp_overload_on ("return", ``constT``);


(************************************************************)
(*****************   Massaging Exceptions   *****************)
(************************************************************)


val take_svc_exception_comb_thm = save_thm("take_svc_exception_comb_thm", take_svc_exception_thm);


val take_undef_instr_exception_comb_thm =
   save_thm("take_undef_instr_exception_comb_thm", MATCH_MP pmc_31_downgrade (take_undef_instr_exception_thm));


val take_prefetch_abort_exception_comb_thm =
   save_thm("take_prefetch_abort_exception_comb_thm", MATCH_MP pmc_31_downgrade (take_prefetch_abort_exception_thm));


val take_data_abort_exception_comb_thm =
   save_thm("take_data_abort_exception_comb_thm", MATCH_MP pmc_31_downgrade (take_data_abort_exception_thm));


val take_irq_exception_comb_thm =
   save_thm("take_irq_exception_comb_thm", MATCH_MP pmc_31_downgrade (take_irq_exception_thm));



(************************************************************)
(***************  A. CPSR simplifications   *****************)
(************************************************************)





(**********************  simplifications ***************************)
(******************* A.1. effects of reading   *********************)


val const_comp_def = Define `const_comp G = (!s s' x. ((G s = ValueState x s') ==> (s=s')))`;

val read_reg_constlem = store_thm(
    "read_reg_constlem",
    ``!n. const_comp (read_reg <|proc:=0|> n)``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
        THEN EVAL_TAC THEN (REPEAT (RW_TAC (srw_ss()) []
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN UNDISCH_ALL_TAC

                           THEN RW_TAC (srw_ss()) [])));

val read_sctlr_constlem = store_thm(
    "read_sctlr_constlem",
    ``const_comp (read_sctlr <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
        THEN EVAL_TAC THEN (REPEAT (RW_TAC (srw_ss()) []
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN UNDISCH_ALL_TAC
                           THEN RW_TAC (srw_ss()) [])));


val read_scr_constlem = store_thm(
    "read_scr_constlem",
    ``const_comp (read_scr <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
        THEN EVAL_TAC THEN (REPEAT (RW_TAC (srw_ss()) []
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN UNDISCH_ALL_TAC
                           THEN RW_TAC (srw_ss()) [])));


val exc_vector_base_constlem = store_thm(
    "exc_vector_base_constlem",
    ``const_comp (exc_vector_base <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
        THEN EVAL_TAC THEN (REPEAT (RW_TAC (srw_ss()) []
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN UNDISCH_ALL_TAC
                           THEN RW_TAC (srw_ss()) [])));



val read_cpsr_effect_lem = store_thm(
    "read_cpsr_effect_lem",
    ``!s H .  ((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) s = (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (s.psrs (0, CPSR)))) s)``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);



val read_cpsr_effect_fixed_lem = store_thm(
    "read_cpsr_effect_fixed_lem",
    ``!s H xI xF.  ((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr with <|M := 16w; I:= xI; F:= xF|>))) s = (read_cpsr <|proc:=0|> >>= (\ (cpsr). H ((s.psrs (0, CPSR))  with <|M := 16w; I:= xI; F:= xF|> ))) s)``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);




val read_cpsr_par_effect_lem = store_thm(
    "read_cpsr_par_effect_lem",
    ``!s A H . (const_comp A) ==> (((A ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, cpsr))) s = ((A ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, s.psrs (0, CPSR)))) s)``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);


val read_cpsr_par_effect_fixed_lem = store_thm(
    "read_cpsr_par_effect_fixed_lem",
    ``!s A H xI xF. (const_comp A) ==> (((A ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, (cpsr with <|M := 16w; I:= xI; F:= xF|>) ))) s = ((A ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, (s.psrs (0, CPSR))  with <|M := 16w; I:= xI; F:= xF|>))) s)``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);



val read_cpsr_par_effect_with_16_lem = store_thm(
    "read_cpsr_par_effect_with_16_lem",
    ``!s A H. (const_comp A) ==> (((A ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, (cpsr with M := 16w) ))) s = ((A ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, (s.psrs (0, CPSR))  with M := 16w))) s)``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);


val read_cpsr_triple_par_effect_lem = store_thm(
    "read_cpsr_triple_par_effect_lem",
    ``!s A B H . (const_comp A) ==> ((((A ||| read_cpsr <|proc:=0|> ||| B) >>= (\ (a, cpsr, b). H (a, cpsr, b))) s)
                                    = (((A ||| read_cpsr <|proc:=0|> ||| B) >>= (\ (a, cpsr, b). H (a, (s.psrs (0, CPSR)),b))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `B b`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_triple_par_effect_lem2 = store_thm(
    "read_cpsr_triple_par_effect_lem2",
    ``!s A B H . (const_comp A) ==> (const_comp B) ==> ((((A ||| B |||  read_cpsr <|proc:=0|>) >>= (\ (a, b, cpsr). H (a, b, cpsr))) s)
                                    = (((A ||| B ||| read_cpsr <|proc:=0|>) >>= (\ (a, b, cpsr). H (a, b, (s.psrs (0, CPSR))))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);


val read_cpsr_triple_par_effect_with_16_lem = store_thm(
    "read_cpsr_triple_par_effect_with_16_lem",
    ``!s A B H . (const_comp A) ==> ((((A ||| read_cpsr <|proc:=0|> ||| B) >>= (\ (a, cpsr, b). H (a, (cpsr with M := 16w), b))) s)
                                    = (((A ||| read_cpsr <|proc:=0|> ||| B) >>= (\ (a, cpsr, b). H (a, ((s.psrs (0, CPSR)) with M := 16w),b))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `B b`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_triple_par_effect_with_16_lem2 = store_thm(
    "read_cpsr_triple_par_effect_with_16_lem2",
    ``!s A B H . (const_comp A) ==> (const_comp B) ==> ((((A ||| B |||  read_cpsr <|proc:=0|>) >>= (\ (a, b, cpsr). H (a, b, (cpsr with M := 16w)))) s)
                                    = (((A ||| B ||| read_cpsr <|proc:=0|>) >>= (\ (a, b, cpsr). H (a, b, ((s.psrs (0, CPSR)) with M := 16w)))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);

val read_cpsr_triple_par_effect_fixed_lem = store_thm(
    "read_cpsr_triple_par_effect_fixed_lem",
    ``!s A B H xI xF. (const_comp A) ==> ((((A ||| read_cpsr <|proc:=0|> ||| B) >>= (\ (a, cpsr, b). H (a, (cpsr with  <|M := 16w; I:= xI; F:= xF|>), b))) s)
                                    = (((A ||| read_cpsr <|proc:=0|> ||| B) >>= (\ (a, cpsr, b). H (a, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>),b))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `B b`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_triple_par_effect_fixed_lem2 = store_thm(
    "read_cpsr_triple_par_effect_fixed_lem2",
    ``!s A B H xI xF. (const_comp A) ==> (const_comp B) ==> ((((A ||| B |||  read_cpsr <|proc:=0|>) >>= (\ (a, b, cpsr). H (a, b, (cpsr with <|M := 16w; I:= xI; F:= xF|>)))) s)
                                    = (((A ||| B ||| read_cpsr <|proc:=0|>) >>= (\ (a, b, cpsr). H (a, b, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>)))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);



val read_cpsr_quintuple_par_effect_lem = store_thm(
    "read_cpsr_quintule_par_effect_lem",
    ``!s A B C D H . (const_comp A) ==>  (const_comp B) ==>  (const_comp C) ==>
                     ((((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, cpsr, d))) s)
                    = (((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, (s.psrs (0, CPSR)), d))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `C b'`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `D b`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_quintuple_par_effect_lem2 = store_thm(
    "read_cpsr_quintule_par_effect_lem2",
    ``!s A B D E H . (const_comp A) ==>  (const_comp B) ==>
                     ((((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, cpsr, d, e))) s)
                    = (((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, (s.psrs (0, CPSR)), d, e))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `D b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `E b'`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_quintuple_par_effect_with_16_lem = store_thm(
    "read_cpsr_quintule_par_effect_with_16_lem",
    ``!s A B C D H . (const_comp A) ==>  (const_comp B) ==>  (const_comp C) ==>
                     ((((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, (cpsr with M := 16w), d))) s)
                    = (((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, ((s.psrs (0, CPSR)) with M := 16w), d))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `C b'`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `D b`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_quintuple_par_effect_with_16_lem2 = store_thm(
    "read_cpsr_quintule_par_effect_with_16_lem2",
    ``!s A B D E H . (const_comp A) ==>  (const_comp B) ==>
                     ((((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, (cpsr with M := 16w), d, e))) s)
                    = (((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, ((s.psrs (0, CPSR)) with M := 16w), d, e))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `D b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `E b'`
       THEN RW_TAC (srw_ss()) []);



val read_cpsr_quintuple_par_effect_fixed_lem = store_thm(
    "read_cpsr_quintule_par_effect_fixed_lem",
    ``!s A B C D H xI xF. (const_comp A) ==>  (const_comp B) ==>  (const_comp C) ==>
                     ((((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, (cpsr with <|M := 16w; I:= xI; F:= xF|>), d))) s)
                    = (((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>), d))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `C b'`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `D b`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_quintuple_par_effect_fixed_lem2 = store_thm(
    "read_cpsr_quintule_par_effect_fixed_lem2",
    ``!s A B D E H xI xF. (const_comp A) ==>  (const_comp B) ==>
                     ((((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, (cpsr with <|M := 16w; I:= xI; F:= xF|>), d, e))) s)
                    = (((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>), d, e))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `D b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `E b'`
       THEN RW_TAC (srw_ss()) []);


val read_reg_read_cpsr_par_effect_lem = store_thm(
    "read_reg_read_cpsr_par_effect_lem",
    ``!s n H. ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, cpsr ))) s = ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, s.psrs (0, CPSR)))) s``,
    RW_TAC (srw_ss()) [read_reg_constlem, read_cpsr_par_effect_lem]);



val read_reg_read_cpsr_par_effect_fixed_lem = store_thm(
    "read_reg_read_cpsr_par_effect_fixed_lem",
    ``!s n H xI xF. ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, (cpsr with <|M := 16w; I:= xI; F:= xF|>)))) s = ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>) ))) s``,
    RW_TAC (srw_ss()) [read_reg_constlem, read_cpsr_par_effect_fixed_lem]);



(**********************  simplifications ***************************)
(************  A.2. computations applied to states   ***************)


val cpsr_simp_lem = store_thm(
    "cpsr_simp_lem",
    ``!s H . (assert_mode 16w s) ==>
       (((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) s)
      = ((read_cpsr <|proc:=0|> >>= (\ (cpsr). H ((s.psrs (0, CPSR)) with M := 16w))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_cpsr_effect_lem, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with M:= 16w))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_simp_ext_lem = store_thm(
    "cpsr_simp_ext_lem",
    ``!s H. (assert_mode 16w s) ==>
             ((s.psrs(0,CPSR)).I = xI) ==>
             ((s.psrs(0,CPSR)).F = xF) ==>
       (((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) s)
      = ((read_cpsr <|proc:=0|> >>= (\ (cpsr). H ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_cpsr_effect_lem, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with <|I := (s.psrs (0,CPSR)).I; F := (s.psrs (0,CPSR)).F; M := 16w|>))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_par_simp_lem = store_thm(
    "cpsr_par_simp_lem",
    ``!s H n. (assert_mode 16w s) ==>
       ((((read_reg <|proc:=0|> n  ||| read_cpsr <|proc:=0|>) >>= (\ (a, cpsr). H (a, cpsr))) s)
      = (((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (a, cpsr). H (a, (s.psrs (0, CPSR)) with M := 16w))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_reg_constlem, read_cpsr_par_effect_lem, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with M:= 16w))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_triple_simp_ext_lem = store_thm(
    "cpsr_triple_simp_ext_lem",
    ``!s H . (assert_mode 16w s) ==>
             ((s.psrs(0,CPSR)).I = xI) ==>
             ((s.psrs(0,CPSR)).F = xF) ==>
       ((((read_reg <|proc:=0|> 15w ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (b,cpsr,d). H (b,cpsr,d))) s)
      = (((read_reg <|proc:=0|> 15w ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (b,cpsr,d). H (b,((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>),d))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_reg_constlem, read_cpsr_triple_par_effect_lem, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with <|I := (s.psrs (0,CPSR)).I; F := (s.psrs (0,CPSR)).F; M := 16w|>))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_triple_simp_ext_lem2 = store_thm(
    "cpsr_triple_simp_ext_lem2",
    ``!s H . (assert_mode 16w s) ==>
             ((s.psrs(0,CPSR)).I = xI) ==>
             ((s.psrs(0,CPSR)).F = xF) ==>
       ((((read_sctlr <|proc := (0 :num)|>
          ||| read_scr <|proc := (0 :num)|>
          |||  read_cpsr <|proc:=0|> ) >>= (\ (sctlr,scr,cpsr). H (sctlr,scr,cpsr))) s)
      = (((read_sctlr <|proc := (0 :num)|>
          ||| read_scr <|proc := (0 :num)|>
          |||  read_cpsr <|proc:=0|> ) >>= (\ (sctlr,scr,cpsr). H (sctlr,scr,((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|> )))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_sctlr_constlem, read_scr_constlem, read_cpsr_triple_par_effect_lem2, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with <|I := (s.psrs (0,CPSR)).I; F := (s.psrs (0,CPSR)).F; M := 16w|> ))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_quintuple_simp_ext_lem = store_thm(
    "cpsr_quintuple_simp_ext_lem",
    ``!s H a n m. (assert_mode 16w s) ==>
             ((s.psrs(0,CPSR)).I = xI) ==>
             ((s.psrs(0,CPSR)).F = xF) ==>
       ((((read_reg <|proc:=0|> a ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (a, b, c, cpsr, d). H (a, b, c, cpsr, d))) s)
      = (((read_reg <|proc:=0|> a ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (a, b, c, cpsr, d). H (a, b, c, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>), d))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_reg_constlem, read_cpsr_quintuple_par_effect_lem, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with <|I := (s.psrs (0,CPSR)).I; F := (s.psrs (0,CPSR)).F; M := 16w|>))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_quintuple_simp_ext_lem2 = store_thm(
    "cpsr_quintuple_simp_ext_lem2",
    ``!s H x . (assert_mode 16w s) ==>
             ((s.psrs(0,CPSR)).I = xI) ==>
             ((s.psrs(0,CPSR)).F = xF) ==>
       ((((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (a, b, cpsr, d, e). H (a, b, cpsr, d, e))) s)
      = (((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (a, b, cpsr, d, e). H (a, b, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>), d, e))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_reg_constlem, exc_vector_base_constlem, read_cpsr_quintuple_par_effect_lem2, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with <|I := (s.psrs (0,CPSR)).I; F := (s.psrs (0,CPSR)).F; M := 16w|>))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);




(**********************  simplifications ***************************)
(******  A.3. computations wrapped by preserving predicate   *******)

val (simp_ext_lem, const_lem_list, H_sig, effect_fixed_lem, additional_spec_list) =
(cpsr_simp_ext_lem,
                  [read_reg_constlem],
                  ``:(ARMpsr ->('a M))``,
                  (read_cpsr_effect_fixed_lem),
                  ([]:Parse.term list));



fun CPSR_SIMP_TAC simp_ext_lem const_lem_list H_sig effect_fixed_lem additional_spec_list s2prime =
    RW_TAC (srw_ss()) []
       THEN EQ_TAC
       THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def, fix_flags_def, fixed_flags_def]
       THEN RW_TAC (srw_ss()) const_lem_list
       THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
       THEN NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [assert_mode_def])
       THENL[ DISJ1_TAC
               THEN MAP_EVERY EXISTS_TAC [``a:'a``, ``s1':arm_state``, s2prime],
              DISJ2_TAC
               THEN EXISTS_TAC ``e:string``,
              DISJ1_TAC
               THEN MAP_EVERY EXISTS_TAC [``a:'a``, ``s1':arm_state``, s2prime],
              DISJ2_TAC
               THEN EXISTS_TAC ``e:string``]
       THEN ASSUME_TAC (SPECL [``xI:bool``, ``(s2.psrs (0,CPSR)).F:bool``, ``s1:arm_state``, mk_var ("H", H_sig)]  (GEN_ALL simp_ext_lem))
       THEN ASSUME_TAC (SPECL [``xI:bool``, ``(s2.psrs (0,CPSR)).F:bool``, ``s2:arm_state``, mk_var ("H", H_sig)]  (GEN_ALL simp_ext_lem))
       THEN ASSUME_TAC (SPECL (List.concat [[``s1:arm_state``], additional_spec_list, [mk_var ("H", H_sig), ``xI:bool``, ``(s2.psrs (0,CPSR)).F:bool``]]) effect_fixed_lem)
       THEN ASSUME_TAC (SPECL (List.concat [[``s2:arm_state``], additional_spec_list, [mk_var ("H", H_sig), ``xI:bool``, ``(s2.psrs (0,CPSR)).F:bool``]])  effect_fixed_lem)
       THEN SPEC_ASSUM_TAC (``!(a:word4) (n:word4) (m:word4). X``, [``aa:word4``, ``nn:word4``, ``mm:word4``])        THEN SPEC_ASSUM_TAC (``!(x:word4). X``, [``x:word4``])
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) [assert_mode_def]
       THEN FULL_SIMP_TAC (srw_ss()) const_lem_list;


val cpsr_simp_rel_lem = store_thm(
    "cpsr_simp_rel_lem",
    ``!H inv2 uf uy.
       (preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) (assert_mode 16w) (inv2) uf uy)
      = (preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr with M := 16w)))(assert_mode 16w) (inv2) uf uy)``,
     RW_TAC (srw_ss()) [cpsr_simp_lem, preserve_relation_mmu_def]);


val cpsr_simp_rel_ext_lem = store_thm(
    "cpsr_simp_rel_ext_lem",
    ``!H inv2 uf uy xI xF.
       (preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) (assert_mode 16w) (inv2) uf (fix_flags xI xF uy))
      = (preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr with <|M := 16w; I:= xI; F:= xF|>)))(assert_mode 16w) (inv2) uf (fix_flags xI xF uy))``,
    FIRST [
            CPSR_SIMP_TAC cpsr_simp_ext_lem
                          [read_reg_constlem]
                          ``:(ARMpsr ->('a M))``
                          (read_cpsr_effect_fixed_lem)
                          ([]:Parse.term list)
                          ``s2':arm_state``
                 THEN NO_TAC,
            CPSR_SIMP_TAC cpsr_simp_ext_lem
                          [read_reg_constlem]
                          ``:(ARMpsr ->('a M))``
                          (read_cpsr_effect_fixed_lem)
                          ([]:Parse.term list)
                          ``s2'':arm_state``]);

val cpsr_par_simp_rel_lem = store_thm(
    "cpsr_par_simp_rel_lem",
    ``!n H inv2 uf uy.
       (preserve_relation_mmu ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (a, cpsr). H (a, cpsr))) (assert_mode 16w) (inv2) uf uy)
      = (preserve_relation_mmu ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (a, cpsr). H (a, cpsr with M := 16w)))(assert_mode 16w) (inv2) uf uy)``,
     RW_TAC (srw_ss()) [cpsr_par_simp_lem, preserve_relation_mmu_def, read_reg_constlem, read_cpsr_par_effect_with_16_lem]);


val cpsr_triple_simp_rel_ext_lem = store_thm(
    "cpsr_triple_simp_rel_ext_lem",
    ``!H inv2 uf uy xI xF.
       (preserve_relation_mmu ((read_reg <|proc:=0|> 15w ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (b,cpsr,d). H (b,cpsr,d))) (assert_mode 16w) (inv2) uf (fix_flags xI xF uy))
      = (preserve_relation_mmu ((read_reg <|proc:=0|> 15w ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (b,cpsr,d). H (b,(cpsr with <|M := 16w; I:= xI; F:= xF|>),d))) (assert_mode 16w) (inv2) uf (fix_flags xI xF uy))``,
    FIRST [
           CPSR_SIMP_TAC cpsr_triple_simp_ext_lem
                  [(SPEC ``15w:word4`` read_reg_constlem)]
                  ``:(word32 # ARMpsr # word32 ->('a M))``
                  (INST_TYPE [alpha |-> Type `:word32`, beta |-> Type `:word32`, gamma |-> alpha] read_cpsr_triple_par_effect_fixed_lem)
                  [``(read_reg <|proc := 0|> 15w):(word32 M)``, ``(read_teehbr <|proc := 0|>):(word32 M)``]
                  ``s2'':arm_state``
               THEN NO_TAC,
           CPSR_SIMP_TAC cpsr_triple_simp_ext_lem
                  [(SPEC ``15w:word4`` read_reg_constlem)]
                  ``:(word32 # ARMpsr # word32 ->('a M))``
                  (INST_TYPE [alpha |-> Type `:word32`, beta |-> Type `:word32`, gamma |-> alpha] read_cpsr_triple_par_effect_fixed_lem)
                  [``(read_reg <|proc := 0|> 15w):(word32 M)``, ``(read_teehbr <|proc := 0|>):(word32 M)``]
                  ``s2':arm_state``]
);


val cpsr_triple_simp_rel_ext_lem2 = store_thm(
    "cpsr_triple_simp_rel_ext_lem2",
    ``!H inv2 uf uy xI xF.
       (preserve_relation_mmu ((read_sctlr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_cpsr <|proc:=0|>) >>= (\ (a,b,cpsr). H (a,b,cpsr))) (assert_mode 16w) (inv2)  uf (fix_flags xI xF uy))
      = (preserve_relation_mmu ((read_sctlr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_cpsr <|proc:=0|>) >>= (\ (a,b,cpsr). H (a,b,(cpsr with <|M := 16w; I:= xI; F:= xF|>)))) (assert_mode 16w) (inv2) uf (fix_flags xI xF uy))``,
    FIRST [
	   CPSR_SIMP_TAC cpsr_triple_simp_ext_lem2
                  [read_sctlr_constlem, read_scr_constlem]
                  ``:(CP15sctlr # CP15scr # ARMpsr ->('a M))``
                  (INST_TYPE [alpha |-> Type `:CP15sctlr`, beta |-> Type `:CP15scr`, gamma |-> alpha] read_cpsr_triple_par_effect_fixed_lem2)
                  [``(read_sctlr <|proc := 0|>):(CP15sctlr M)``, ``(read_scr <|proc := 0|>):(CP15scr M)``]
                  ``s2':arm_state``
             THEN NO_TAC,
	   CPSR_SIMP_TAC cpsr_triple_simp_ext_lem2
                  [read_sctlr_constlem, read_scr_constlem]
                  ``:(CP15sctlr # CP15scr # ARMpsr ->('a M))``
                  (INST_TYPE [alpha |-> Type `:CP15sctlr`, beta |-> Type `:CP15scr`, gamma |-> alpha] read_cpsr_triple_par_effect_fixed_lem2)
                  [``(read_sctlr <|proc := 0|>):(CP15sctlr M)``, ``(read_scr <|proc := 0|>):(CP15scr M)``]
                  ``s2'':arm_state``]
);


val cpsr_quintuple_simp_rel_ext_lem = store_thm(
    "cpsr_quintuple_simp_rel_ext_lem",
    ``!aa nn mm H inv2 uf uy xI xF .
       (preserve_relation_mmu ((read_reg <|proc:=0|> aa ||| read_reg <|proc:=0|> nn ||| read_reg <|proc:=0|> mm ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (aa, bb, cc, cpsr, dd). H (aa, bb, cc, cpsr, dd))) (assert_mode 16w) (inv2)  uf (fix_flags xI xF uy))
      = (preserve_relation_mmu ((read_reg <|proc:=0|> aa ||| read_reg <|proc:=0|> nn ||| read_reg <|proc:=0|> mm ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (aa, bb, cc, cpsr, dd). H (aa, bb, cc, (cpsr with <|M := 16w; I:= xI; F:= xF|>), dd))) (assert_mode 16w) (inv2)  uf (fix_flags xI xF uy))``,
FIRST
     [CPSR_SIMP_TAC cpsr_quintuple_simp_ext_lem
                  [read_reg_constlem]
                  ``:(word32 # word32 # word32 # ARMpsr # word32->('a M))``
                  (INST_TYPE [alpha |-> Type `:word32`, beta |-> Type `:word32`, gamma |-> Type `:word32`, delta |-> Type `:word32`, Type `:'e` |-> alpha] read_cpsr_quintuple_par_effect_fixed_lem)
                  [``(read_reg <|proc:=0|> aa) :word32 M``, ``(read_reg <|proc:=0|> nn) :word32 M`` , ``(read_reg <|proc:=0|> mm) :word32 M`` , ``(read_teehbr <|proc:=0|> ):word32 M`` ]
                  ``s2'':arm_state``
          THEN NO_TAC,
      CPSR_SIMP_TAC cpsr_quintuple_simp_ext_lem
                  [read_reg_constlem]
                  ``:(word32 # word32 # word32 # ARMpsr # word32->('a M))``
                  (INST_TYPE [alpha |-> Type `:word32`, beta |-> Type `:word32`, gamma |-> Type `:word32`, delta |-> Type `:word32`, Type `:'e` |-> alpha] read_cpsr_quintuple_par_effect_fixed_lem)
                  [``(read_reg <|proc:=0|> aa) :word32 M``, ``(read_reg <|proc:=0|> nn) :word32 M`` , ``(read_reg <|proc:=0|> mm) :word32 M`` , ``(read_teehbr <|proc:=0|> ):word32 M`` ]
                  ``s2':arm_state``
      ]);


val cpsr_quintuple_simp_rel_ext_lem2 = store_thm(
    "cpsr_quintuple_simp_rel_ext_lem2",
    ``!x H inv2 uf uy xI xF.
       (preserve_relation_mmu (((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (a, b, cpsr, d, e). H (a, b, cpsr, d, e)))) (assert_mode 16w) (inv2)  uf (fix_flags xI xF uy))
      = (preserve_relation_mmu (((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (a, b, cpsr, d, e). H (a, b, (cpsr with <|M := 16w; I:= xI; F:= xF|>), d, e))))(assert_mode 16w) (inv2)  uf (fix_flags xI xF uy))``,
    FIRST
      [   CPSR_SIMP_TAC cpsr_quintuple_simp_ext_lem2
                  [read_reg_constlem, exc_vector_base_constlem, read_scr_constlem, read_sctlr_constlem]
                  ``:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr ->('a M))``
                  (INST_TYPE [alpha |-> Type `:word32`, beta |-> Type `:word32`, gamma |-> Type `:CP15scr`, delta |-> Type `:CP15sctlr`, Type `:'e` |-> alpha] read_cpsr_quintuple_par_effect_fixed_lem2)
                  [``(read_reg <|proc:=0|> x) :word32 M``, ``(exc_vector_base <|proc:=0|>) :word32 M`` , ``(read_scr <|proc:=0|>) :CP15scr M`` , ``(read_sctlr <|proc:=0|> ):CP15sctlr M`` ]
                  ``s2':arm_state``
               THEN NO_TAC,
         CPSR_SIMP_TAC cpsr_quintuple_simp_ext_lem2
                  [read_reg_constlem, exc_vector_base_constlem, read_scr_constlem, read_sctlr_constlem]
                  ``:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr ->('a M))``
                  (INST_TYPE [alpha |-> Type `:word32`, beta |-> Type `:word32`, gamma |-> Type `:CP15scr`, delta |-> Type `:CP15sctlr`, Type `:'e` |-> alpha] read_cpsr_quintuple_par_effect_fixed_lem2)
                  [``(read_reg <|proc:=0|> x) :word32 M``, ``(exc_vector_base <|proc:=0|>) :word32 M`` , ``(read_scr <|proc:=0|>) :CP15scr M`` , ``(read_sctlr <|proc:=0|> ):CP15sctlr M`` ]
                  ``s2'':arm_state``]
);




(************************************************************)
(**********  B. registers, memory, minor things   ***********)
(************************************************************)



(* ========= read_reg ============*)


val _ = g `preserve_relation_mmu (LookUpRName <|proc:=0|> (t,M)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = go_on 1;
val LookUpRName_thm =  save_thm("LookUpRName_thm", top_thm());



g `(~ access_violation s) ==> (((LookUpRName <|proc := 0|> (nw,16w)) s) = ValueState reg s') ==> (reg IN  {RName_0usr; RName_1usr; RName_2usr; RName_3usr; RName_4usr; RName_5usr; RName_6usr; RName_7usr; RName_8usr; RName_9usr; RName_10usr; RName_11usr; RName_12usr; RName_SPusr; RName_LRusr; RName_PC})`;
e(EVAL_TAC);
e(RW_TAC (srw_ss()) [] THEN METIS_TAC []);
val lookup_read__reg_help_lem1 = top_thm();


g `(nw <> 15w) ==> (access_violation s) ==> ((((LookUpRName <|proc := 0|> (nw,16w)  >>=  (λrname. read__reg <|proc := 0|> rname)) s) = ValueState ARB s)) `;
e(EVAL_TAC);
e(RW_TAC (srw_ss())  []);
e(IMP_RES_TAC (blastLib.BBLAST_PROVE ``((nw:word4) <> (0w:word4)) ==> (nw <> 1w) ==> (nw <> 2w) ==> (nw <> 3w) ==> (nw <> 4w)  ==> (nw <> 5w) ==> (nw <> 6w) ==> (nw <> 7w) ==> (nw <> 8w) ==> (nw <> 9w) ==> (nw <> 10w) ==> (nw <> 11w) ==> (nw <> 12w)  ==> (nw <> 13w) ==> (nw <> 14w) ==> (nw = 15w)``));
val lookup_read__reg_help_lem2 = top_thm();


g `(nw = 15w) ==> (access_violation s) ==>  (((LookUpRName <|proc := 0|> (nw,16w)  >>=  (λrname. read__reg <|proc := 0|> rname)) s) = Error "LookUpRName: n = 15w") `;
e(EVAL_TAC);
e(RW_TAC (srw_ss())  []);
val lookup_read__reg_help_lem3 = top_thm();


g ` preserve_relation_mmu (LookUpRName <|proc := 0|> (nw,16w) >>=  (λrname. read__reg <|proc := 0|> rname)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(RW_TAC (srw_ss()) [preserve_relation_mmu_def, empty_unt_def, empty_sim_def]);
e(`access_violation s1 = access_violation s2` by METIS_TAC [similar_def]);
e(Cases_on `access_violation s1`);
(* access violation from beginning *)
e(`access_violation s2` by FULL_SIMP_TAC (srw_ss()) []);
e(Cases_on `nw = 15w`);
(* nw = 15 *)
e(IMP_RES_TAC lookup_read__reg_help_lem3);
e(RW_TAC (srw_ss()) []);
(* nw <> 15 *)
e(IMP_RES_TAC lookup_read__reg_help_lem2);
e(RW_TAC (srw_ss()) [untouched_refl]);
(* no access violation from beginning *)
e(`~ access_violation s2` by FULL_SIMP_TAC (srw_ss()) []);
e(ASSUME_TAC (SPECL [``nw:word4``,``16w:word5``] (GEN_ALL LookUpRName_thm)));
e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def, empty_sim_def, empty_unt_def]);
e(SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``]));
e(UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);
(* received same value in Lookup *)
e(`access_violation s1' = access_violation s2'` by METIS_TAC [similar_def]);
e(FULL_SIMP_TAC (srw_ss()) [seqT_def, read__reg_def, constT_def, readT_def]);
e(RW_TAC (srw_ss()) []);
e(ASSUME_TAC  (SPECL [``s1':arm_state``, ``s1:arm_state``, ``a:RName``, ``nw:word4``] (GEN_ALL lookup_read__reg_help_lem1)));
e(FULL_SIMP_TAC (srw_ss()) [similar_def, equal_user_register_def]);
e(SPEC_ASSUM_TAC (``!(reg:RName). X``, [``a:RName``]));
e(UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);
(* Error in Lookup *)
e(RW_TAC (srw_ss()) [seqT_def]);
val lookup_read__reg_thm = top_thm();
add_to_simplist lookup_read__reg_thm;


g `preserve_relation_mmu (read_reg_mode <|proc:=0|> (nw, 16w)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
go_on 1;
val read_reg_mode_thm =  save_thm ("read_reg_mode_thm", (MATCH_MP extras_lem2 (top_thm())));


g `preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (λcpsr. read_reg_mode <|proc:=0|> (n,16w))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
go_on 1;
val read_cpsr_read_reg_mode_16_thm = save_thm("read_cpsr_read_reg_mode_16_thm", top_thm());


g `preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (λcpsr. read_reg_mode <|proc:=0|> (n,cpsr.M))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(ASSUME_TAC (SPECL [``(\c. read_reg_mode <|proc:=0|> (n, c.M))``, ``assert_mode 16w``] (INST_TYPE [alpha |-> Type `:word32`] cpsr_simp_rel_lem)));
e(ASSUME_TAC read_cpsr_read_reg_mode_16_thm);
e(FULL_SIMP_TAC (srw_ss()) []);
val read_cpsr_read_reg_mode_thm = top_thm();
add_to_simplist read_cpsr_read_reg_mode_thm;


val (read_reg_empty_thm, _) =  prove_it ``read_reg <|proc:=0|> n`` ``assert_mode 16w`` ``assert_mode 16w`` ``empty_unt`` ``empty_sim``;
val read_reg_thm = save_thm("read_reg_thm", MATCH_MP extras_lem2 read_reg_empty_thm);





(* ========= write_reg ============*)


g `(nw <> 15w) ==> (access_violation s) ==> ((((LookUpRName <|proc := 0|> (nw,16w)  >>=  ( \ rname. write__reg <|proc := 0|> rname value)) s) = (ValueState () s))) `;
e(EVAL_TAC);
e(RW_TAC (srw_ss())  []
   THEN `!(x:unit). x = ()` by (Cases_on `x` THEN EVAL_TAC)
   THEN SPEC_ASSUM_TAC (``!x. X``, [``ARB:unit``])
   THEN FULL_SIMP_TAC (srw_ss()) []);
e(IMP_RES_TAC (blastLib.BBLAST_PROVE ``((nw:word4) <> (0w:word4)) ==> (nw <> 1w) ==> (nw <> 2w) ==> (nw <> 3w) ==> (nw <> 4w)  ==> (nw <> 5w) ==> (nw <> 6w) ==> (nw <> 7w) ==> (nw <> 8w) ==> (nw <> 9w) ==> (nw <> 10w) ==> (nw <> 11w) ==> (nw <> 12w)  ==> (nw <> 13w) ==> (nw <> 14w) ==> (nw = 15w)``));
val lookup_write__reg_help_lem2 = top_thm();


g `(nw = 15w) ==> (access_violation s) ==>  (((LookUpRName <|proc := 0|> (nw,16w)  >>=  (λrname. write__reg <|proc := 0|> rname value)) s) = Error "LookUpRName: n = 15w") `;
e(EVAL_TAC);
e(RW_TAC (srw_ss())  []);
val lookup_write__reg_help_lem3 = top_thm();


g ` preserve_relation_mmu (LookUpRName <|proc := 0|> (nw,16w) >>=  (λrname. write__reg <|proc := 0|> rname value)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(RW_TAC (srw_ss()) [preserve_relation_mmu_def, empty_unt_def, empty_sim_def]);
e(`access_violation s1 = access_violation s2` by METIS_TAC [similar_def]);
e(Cases_on `access_violation s1`);
(* access violation from beginning *)
e(`access_violation s2` by FULL_SIMP_TAC (srw_ss()) []);
e(Cases_on `nw = 15w`);
(* nw = 15 *)
e(IMP_RES_TAC lookup_write__reg_help_lem3);
e(RW_TAC (srw_ss()) []);
(* nw <> 15 *)
e(IMP_RES_TAC lookup_write__reg_help_lem2);
e(RW_TAC (srw_ss()) [untouched_refl]);
(* no access violation from beginning *)
e(`~ access_violation s2` by FULL_SIMP_TAC (srw_ss()) []);
e(ASSUME_TAC (SPECL [``nw:word4``,``16w:word5``] (GEN_ALL LookUpRName_thm)));
e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def, empty_sim_def, empty_unt_def]);
e(SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``]));
e(UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);
(* received same value in Lookup *)
e(DISJ1_TAC);
e(`access_violation s1' = access_violation s2'` by METIS_TAC [similar_def]);
e(Cases_on `access_violation s2'` THEN FULL_SIMP_TAC (srw_ss()) [seqT_def, write__reg_def, constT_def, writeT_def]);
e(RW_TAC (srw_ss()) []);
(*** untouched 1 *)
e(IMP_RES_TAC  (SPECL [``s1':arm_state``, ``s1:arm_state``, ``a:RName``, ``nw:word4``] (GEN_ALL lookup_read__reg_help_lem1))
               THEN FULL_SIMP_TAC (srw_ss()) [assert_mode_def, untouched_def, LET_DEF]
               THEN RW_TAC (srw_ss()) []
               THEN REPEAT (UNDISCH_MATCH_TAC ``(reg:RName) <> rn_u``)
               THEN EVAL_TAC
               THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);
(*** untouched 2 *)
e (IMP_RES_TAC  (SPECL [``s2':arm_state``, ``s2:arm_state``, ``a:RName``, ``nw:word4``] (GEN_ALL lookup_read__reg_help_lem1))
               THEN FULL_SIMP_TAC (srw_ss()) [assert_mode_def, untouched_def, LET_DEF]
               THEN RW_TAC (srw_ss()) []
               THEN REPEAT (UNDISCH_MATCH_TAC ``(reg:RName) <> rn_u``)
               THEN EVAL_TAC
               THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);
(*** mode 1 *)
e(FULL_SIMP_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def]);
(*** mode w *)
e(FULL_SIMP_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def]);
(*** similar *)
e(UNDISCH_TAC ``similar g s1' s2'``);
e(EVAL_TAC);
e((REPEAT (STRIP_TAC)) THEN FULL_SIMP_TAC (srw_ss()) []);
e(IMP_RES_TAC untouched_mmu_setup_lem);
e(ASSUME_TAC (SPECL [``s1':arm_state``, ``s1' with registers updated_by ((0,a) =+ value)``, ``g:word32``] trivially_untouched_av_lem));
e(ASSUME_TAC (SPECL [``s2':arm_state``, ``s2' with registers updated_by ((0,a) =+ value)``, ``g:word32``] trivially_untouched_av_lem));
e(FULL_SIMP_TAC (srw_ss()) []);
(* Error in Lookup *)
e(RW_TAC (srw_ss()) [seqT_def]);
val lookup_write__reg_thm = top_thm();
add_to_simplist lookup_write__reg_thm;


g `preserve_relation_mmu (write_reg_mode <|proc:=0|> (nw, 16w) value) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
go_on 1;
val write_reg_mode_thm =  save_thm ("write_reg_mode_thm", (MATCH_MP extras_lem2 (top_thm())));


g `preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (λcpsr. write_reg_mode <|proc:=0|> (n,16w) value)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
go_on 1;
val read_cpsr_read_reg_mode_16_thm = save_thm("read_cpsr_write_reg_mode_16_thm", top_thm());


g `preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (λcpsr. write_reg_mode <|proc:=0|> (n,cpsr.M) value)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(ASSUME_TAC (SPECL [``(\c. write_reg_mode <|proc:=0|> (n, c.M) value)``, ``assert_mode 16w``] (INST_TYPE [alpha |-> Type `:unit`] cpsr_simp_rel_lem)));
e(ASSUME_TAC read_cpsr_read_reg_mode_16_thm);
e(FULL_SIMP_TAC (srw_ss()) []);
val read_cpsr_write_reg_mode_thm = top_thm();
add_to_simplist read_cpsr_write_reg_mode_thm;


val (write_reg_empty_thm, _) =  prove_it ``write_reg <|proc:=0|> n value`` ``assert_mode 16w`` ``assert_mode 16w`` ``empty_unt`` ``empty_sim``;
val write_reg_thm = save_thm("write_reg_thm", MATCH_MP extras_lem2 write_reg_empty_thm);



(* ===================================================================== *)


(* arch version *)

val arch_version_alternative_def = store_thm(
    "arch_version_alternative_def",
    ``arch_version ii = (read_arch ii >>= (\arch. constT(version_number arch)))``,
    RW_TAC (srw_ss()) [arch_version_def, constT_def, seqT_def]);

g `preserve_relation_mmu (arch_version <|proc:=0|>)
	      (assert_mode 16w) (assert_mode  16w) strict_unt empty_sim`;
e(RW_TAC (srw_ss()) [arch_version_alternative_def]);
go_on 1;
val arch_version_thm = save_thm("arch_version_thm", (MATCH_MP extras_lem4 (SPEC_ALL (top_thm()))));


(* ===================================================================== *)

(* address mode *)


g `preserve_relation_mmu (thumb_expand_imm_c (imm12,c_in)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(RW_TAC (srw_ss()) [thumb_expand_imm_c_def, LET_DEF]
    THEN Cases_on `(9 >< 8) (imm12:word12) = (0w:word2)` THEN Cases_on `(9 >< 8) imm12 = (1w:word2)` THEN Cases_on `(9 >< 8) imm12 = (2w:word2)` THEN Cases_on `(9 >< 8) imm12 = (3w:word2)`
    THEN ASSUME_TAC (blastLib.BBLAST_PROVE ``((((9 >< 8) (imm12:word12)) <> (0w:word2)) /\ (((9 >< 8) imm12) <> (1w:word2)) /\ (((9 >< 8) imm12) <> (2w:word2)) /\ (((9 >< 8) imm12) <> (3w:word2))) ==> F``)
    THEN UNDISCH_ALL_TAC
    THEN RW_TAC (srw_ss()) []);
go_on 11;
val thumb_expand_imm_c_thm = save_thm("thumb_expand_imm_c_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));



val _ = g `preserve_relation_mmu (address_mode1 <|proc:=0|> enc mode1) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = e(Cases_on `mode1` THEN RW_TAC (srw_ss()) [address_mode1_def, LET_DEF]);
val _ = go_on 1;
val _ = e(PairedLambda.GEN_BETA_TAC);
val _ = go_on 1;
val _ = go_on 1;
val address_mode1_thm = save_thm("address_mode1_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));


val _ = g `preserve_relation_mmu (address_mode2 <|proc:=0|> indx addr rn mode2) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = e(Cases_on `mode2` THEN RW_TAC (srw_ss()) [address_mode2_def, LET_DEF]);
val _ = go_on 4;
val _ = e(PairedLambda.GEN_BETA_TAC);
val _ = go_on 1;
val address_mode2_thm = save_thm("address_mode2_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));


val _ = g `preserve_relation_mmu (address_mode3 <|proc:=0|> indx addr rn mode3) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = e(Cases_on `mode3` THEN RW_TAC (srw_ss()) [address_mode3_def, LET_DEF]);
val _ = go_on 4;
val _ = e(PairedLambda.GEN_BETA_TAC);
val _ = go_on 1;
val address_mode3_thm = save_thm("address_mode3_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));



(* ===================================================================== *)


val _ = g `preserve_relation_mmu (read_memA_with_priv <|proc:=0|> (addr, n, p)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = go_on 1;


val read_memA_with_priv_thm = prove_and_save_s (``read_memA_with_priv <|proc:=0|> (addr, n, p)``, "read_memA_with_priv_thm");


val read_memA_with_priv_loop_body_thm = prove_and_save (``λi. read_memA_with_priv <|proc:=0|> (address + n2w i,1,privileged)``, "read_memA_with_priv_loop_body_thm");

val read_memA_with_priv_loop_thm = store_thm(
    "read_memA_with_priv_loop_thm",
    ``preserve_relation_mmu (forT 0 (size − 1)
             (λi.
                read_memA_with_priv <|proc:=0|>
                  (address + n2w i,1,privileged))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim``,
   ASSUME_TAC read_memA_with_priv_loop_body_thm
      THEN FULL_SIMP_TAC (srw_ss()) [trans_empty_unt_thm, reflex_empty_unt_thm, reflex_empty_sim_thm, forT_preserving_thm]);
val _ = add_to_simplist read_memA_with_priv_loop_thm;

val _ = g `preserve_relation_mmu (read_memU_with_priv <|proc:=0|> (address:word32, size:num, privileged:bool)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = e(FULL_SIMP_TAC (srw_ss()) [read_memU_with_priv_def, LET_DEF]);
val _ = go_on 1;
val read_memU_with_priv_thm = save_thm ("read_memU_with_priv_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));


val write_memA_with_priv_empty_thm = prove_and_save (``write_memA_with_priv <|proc:=0|> (addr, size, p) vl``, "write_memA_with_priv_empty_thm");
val write_memA_with_priv_thm = save_thm("write_memA_wih_priv_thm", (MATCH_MP extras_lem2 (SPEC_ALL write_memA_with_priv_empty_thm)));

val write_memA_with_priv_loop_body_thm = prove_and_save (``λi. write_memA_with_priv <|proc:=0|> (address + n2w i,1,privileged) [EL i value]``, "write_memA_with_priv_loop_body_thm");

val write_memA_with_priv_loop_thm = store_thm(
    "write_memA_with_priv_loop_thm",
    ``preserve_relation_mmu (forT 0 (size − 1) (λi. write_memA_with_priv <|proc:=0|> (address + n2w i,1,privileged) [EL i value])) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim``,
   ASSUME_TAC write_memA_with_priv_loop_body_thm
      THEN FULL_SIMP_TAC (srw_ss()) [trans_empty_unt_thm, reflex_empty_unt_thm, reflex_empty_sim_thm, forT_preserving_thm]);
val _ = add_to_simplist write_memA_with_priv_loop_thm;

val write_memU_with_priv_empty_thm = prove_and_save (``write_memU_with_priv <|proc:=0|> (address:word32, size:num, privileged:bool) x``, "write_memU_with_priv_empty_thm");
val write_memU_with_priv_thm = save_thm ("write_memU_with_priv_thm", (MATCH_MP extras_lem2 (SPEC_ALL (write_memU_with_priv_empty_thm))));


val _ = g `preserve_relation_mmu (set_exclusive_monitors <|proc:=0|> (addr, n)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = e(FULL_SIMP_TAC (srw_ss()) [set_exclusive_monitors_def, LET_DEF]);
val _ = go_on 1;
val set_exclusive_monitors_thm = save_thm("set_exclusive_monitors_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));


val _ = g `preserve_relation_mmu
  ((λ(passed,state').
      write_monitor <|proc := 0|> (monitor with state := state') >>=
      (λu. return passed))
     ((λ(local_passed,x').
         (λ(passed,x).
            (if passed then
               (λy. (λ(u,x). (T,x)) (monitor.ClearExclusiveLocal 0 y))
             else
               (λy. (F,y))) x)
           ((if memaddrdesc.memattrs.shareable then
               (λy.
                  (λ(global_passed,x). (local_passed ∧ global_passed,x))
                    (monitor.IsExclusiveGlobal
                       (memaddrdesc.paddress,<|proc := 0|>,n) y))
             else
               (λy. (local_passed,y))) x'))
        (monitor.IsExclusiveLocal (memaddrdesc.paddress,<|proc := 0|>,n)
           monitor.state))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim `;
val _ = e(Cases_on `(monitor.IsExclusiveLocal (memaddrdesc.paddress,<|proc := 0|>,n)
           monitor.state)`
   THEN RW_TAC (srw_ss()) []
   THEN Cases_on `(monitor.IsExclusiveGlobal
              (memaddrdesc.paddress,<|proc := 0|>,n) r)`
   THEN RW_TAC (srw_ss()) []
   THEN Cases_on ` (monitor.ClearExclusiveLocal 0 r')`
   THEN Cases_on ` (monitor.ClearExclusiveLocal 0 r)`
   THEN RW_TAC (srw_ss()) []);
val _ = go_on 4;
val exclusive_monitors_pass_help_thm = save_thm("exclusive_monitors_pass_help_thm", top_thm());
val _ = add_to_simplist exclusive_monitors_pass_help_thm;


val _= g `preserve_relation_mmu (exclusive_monitors_pass <|proc:=0|> (addr,n)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = e(FULL_SIMP_TAC (srw_ss()) [exclusive_monitors_pass_def, seqE_def, constE_def, LET_DEF]);
val _ = go_on 1;
val exclusive_monitors_pass_thm = save_thm("exclusive_monitors_pass_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));



(************************************************************)
(**************  C. more PSR related lemmas  ****************)
(************************************************************)



val read_cpsr_thm = prove_and_save_s(``read_cpsr <|proc:=0|>``, "read_cpsr_thm");


val read_cpsr_abs_thm = store_thm("read_cpsr_abs_thm",
  ``!uy. preserve_relation_mmu_abs (\cp. read_cpsr <|proc:=0|>) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints uy``,
 (RW_TAC (srw_ss()) [preserve_relation_mmu_abs_def,similar_def, assert_mode_def, priv_mode_constraints_def, read_cpsr_def,read__psr_def,readT_def,untouched_def] THEN FULL_SIMP_TAC (srw_ss()) []));


val read_cpsr_comb_thm = store_thm("read_cpsr_comb_thm",
  ``!invr uy. preserve_relation_mmu (read_cpsr <|proc:=0|>) invr invr empty_unt uy``,
 (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def, assert_mode_def,read_cpsr_def,read__psr_def,readT_def,untouched_def, empty_unt_def] THEN FULL_SIMP_TAC (srw_ss()) []));


val write_cpsr_thm = store_thm(
    "write_cpsr_thm",
    `` !k k'. preserve_relation_mmu ( write_cpsr <|proc :=0 |> (cpsr with <|I := xI; F := xF; M := k'|>)) (assert_mode k) (assert_mode k') empty_unt (fix_flags xI xF empty_sim)``,
   `!psr. (psr <> CPSR) ==> (0 <> PSRName2num psr)` by (EVAL_TAC THEN RW_TAC (srw_ss()) [])
      THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def,write_cpsr_def,write__psr_def,writeT_def,similar_def,untouched_def,assert_mode_def, fix_flags_def, fixed_flags_def, empty_sim_def, empty_unt_def]
      THEN EVAL_TAC
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [equal_user_register_def]
      THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s1 with psrs updated_by ((0,CPSR) =+ cpsr with <|I := xI; F := (s2.psrs (0,CPSR)).F; M := k'|>)``, ``g:word32``]  trivially_untouched_av_lem)
      THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``s2 with psrs updated_by ((0,CPSR) =+ cpsr with <|I := xI; F := (s2.psrs (0,CPSR)).F; M := k'|>)``, ``g:word32``]  trivially_untouched_av_lem)
      THEN UNDISCH_ALL_TAC
      THEN RW_TAC (srw_ss()) []);



(* write cpsr with several components*)


val write_cpsr_E_IFM_thm = store_thm(
    "write_cpsr_E_IFM_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|E := something; I := xI; F := xF; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with E := something)`
      THEN `cpsr with <|E := something; M := 16w; I := xI; F := xF|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
val _ = add_to_simplist  write_cpsr_E_IFM_thm;

val write_cpsr_IT_IFM_thm = store_thm(
    "write_cpsr_IT_IFM_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|IT := something; I := xI; F := xF; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with IT := something)`
      THEN `cpsr with <|IT := something; M := 16w; I := xI; F := xF|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
val _ = add_to_simplist  write_cpsr_IT_IFM_thm;


val write_cpsr_GE_IFM_thm = store_thm(
    "write_cpsr_GE_IFM_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|GE := something; I := xI; F := xF; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with GE := something)`
      THEN `cpsr with <|GE := something; M := 16w; I := xI; F := xF|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
val _ = add_to_simplist  write_cpsr_GE_IFM_thm;


val write_cpsr_Q_IFM_thm = store_thm(
    "write_cpsr_Q_IFM_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|Q := something; I := xI; F := xF; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with Q := something)`
      THEN `cpsr with <|Q := something; M := 16w; I := xI; F := xF|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
val _ = add_to_simplist  write_cpsr_Q_IFM_thm;



val write_cpsr_J_T_IFM_thm = store_thm(
    "write_cpsr_J_T_IFM_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|J := j; I := xI; F := xF;  T := t; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with <|J := j; T := t|>)`
      THEN `cpsr with <|J := j; T := t; M := 16w; I := xI; F := xF|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
val _ = add_to_simplist  write_cpsr_J_T_IFM_thm;


val write_cpsr_flags_IFM_thm = store_thm(
    "write_cpsr_flags_IFM_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|N := n; Z := z; C := c; V := v; I := xI; F := xF; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with <|N := n; Z := z; C := c; V := v|>)`
      THEN `cpsr with <|N := n; Z := z; C := c; V := v; M := 16w; I := xI; F := xF|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
val _ = add_to_simplist  write_cpsr_flags_IFM_thm;


val write_cpsr_all_components_thm = store_thm(
    "write_cpsr_all_components_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|N:=n; Z:=z; C:=c; V:=v; Q:=q; IT:=it; J:=j; GE:=ge; E:=e; T:=t; I := xI; F := xF; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with <|N:=n; Z:=z; C:=c; V:=v; Q:=q; IT:=it; J:=j; GE:=ge; E:=e; T:=t|>)`
      THEN `cpsr with <|N:=n; Z:=z; C:=c; V:=v; Q:=q; IT:=it; J:=j; GE:=ge; E:=e; T:=t; I := xI; F := xF; M := 16w|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
val _ = add_to_simplist  write_cpsr_all_components_thm;



(*************  applications of simplifications  ********************)



(* write e *)

val _ = g `!e. preserve_relation_mmu (write_e <|proc:=0|> e) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = e(STRIP_TAC);
val _ = e(ASSUME_TAC (SPECL [``(write_e <|proc := 0|> e):(unit M)``, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``, ``empty_unt``, ``empty_sim``] (INST_TYPE [alpha |-> type_of(``()``)] fix_flags_lem)));
val _ = e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
val _ = e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
val _ = e(RW_TAC (srw_ss()) [write_e_def]);
val _ = e(ASSUME_TAC (SPECL [``(λcpsr. write_cpsr <|proc := 0|> (cpsr with E := e)):(ARMpsr -> unit M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> type_of(``()``)] cpsr_simp_rel_ext_lem)));
val _ = e(FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 1;
val write_e_empty_thm = save_thm("write_e_empty_thm", top_thm());
val write_e_thm = save_thm("write_e_thm", MATCH_MP extras_lem2 (SPEC_ALL write_e_empty_thm));


(* write ge *)

val _ = g `!e. preserve_relation_mmu (write_ge <|proc:=0|> ge) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = e(STRIP_TAC);
val _ = e(ASSUME_TAC (SPECL [``(write_ge <|proc := 0|> ge):(unit M)``, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``, ``empty_unt``, ``empty_sim``] (INST_TYPE [alpha |-> type_of(``()``)] fix_flags_lem)));
val _ = e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
val _ = e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
val _ = e(RW_TAC (srw_ss()) [write_ge_def]);
val _ = e(ASSUME_TAC (SPECL [``(λcpsr. write_cpsr <|proc := 0|> (cpsr with GE := ge)):(ARMpsr -> unit M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> type_of(``()``)] cpsr_simp_rel_ext_lem)));
val _ = e(FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 1;
val write_ge_empty_thm = save_thm("write_ge_empty_thm", top_thm());
val write_ge_thm = save_thm("write_ge_thm", MATCH_MP extras_lem2 (SPEC_ALL write_ge_empty_thm));



(* write is et state*)


val _ = g `!e. preserve_relation_mmu (write_isetstate <|proc:=0|> isetstate) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = e(STRIP_TAC);
val _ = e(ASSUME_TAC (SPECL [``(write_isetstate <|proc := 0|> isetstate):(unit M)``, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``, ``empty_unt``, ``empty_sim``] (INST_TYPE [alpha |-> type_of(``()``)] fix_flags_lem)));
val _ = e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
val _ = e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
val _ = e(RW_TAC (srw_ss()) [write_isetstate_def]);
val _ = e(ASSUME_TAC (SPECL [``(λcpsr. write_cpsr <|proc := 0|> (cpsr with <|J := (isetstate:word2) ' 1; T := isetstate ' 0 |>)):(ARMpsr -> unit M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> type_of(``()``)] cpsr_simp_rel_ext_lem)));
val _ = e(FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 1;
val write_isetstate_empty_thm = save_thm("write_isetstate_empty_thm", top_thm());
val write_isetstate_thm = save_thm("write_isetstate_thm", MATCH_MP extras_lem2 (SPEC_ALL write_isetstate_empty_thm));



(* write flags *)

val _ = g `!e. preserve_relation_mmu (write_flags<|proc:=0|> (n,z,c,v)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = e(STRIP_TAC);
val _ = e(ASSUME_TAC (SPECL [``(write_flags <|proc := 0|> (n,z,c,v)):(unit M)``, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``, ``empty_unt``, ``empty_sim``] (INST_TYPE [alpha |-> type_of(``()``)] fix_flags_lem)));
val _ = e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
val _ = e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
val _ = e(RW_TAC (srw_ss()) [write_flags_def]);
val _ = e(ASSUME_TAC (SPECL [``(λcpsr. write_cpsr <|proc := 0|> (cpsr with <|N := n; Z := z; C := c; V := v|>)):(ARMpsr -> unit M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> type_of(``()``)] cpsr_simp_rel_ext_lem)));
val _ = e(FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 1;
val write_flags_empty_thm = save_thm("write_flags_empty_thm", top_thm());
val write_flags_thm = save_thm("write_flags_thm", MATCH_MP extras_lem2 (SPEC_ALL write_flags_empty_thm));




(* IT advance *)
val _ = g `preserve_relation_mmu (read_cpsr <|proc:=0|> >>=
            (λcpsr.
               if (cpsr.IT = 0w) ∨ cpsr.T then
                 write_cpsr <|proc:=0|> (cpsr with IT := ITAdvance cpsr.IT)
               else
                 errorT "IT_advance: unpredictable")) (assert_mode 16w) (assert_mode 16w) (empty_unt) (fix_flags xI xF empty_sim)`;
val _ = e(ASSUME_TAC (SPECL [``(λcpsr. if (cpsr.IT = 0w) ∨ cpsr.T then
                 write_cpsr <|proc:=0|> (cpsr with IT := ITAdvance cpsr.IT)
               else
                 errorT "IT_advance: unpredictable"):(ARMpsr -> unit M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> type_of(``()``)] cpsr_simp_rel_ext_lem)));
val _ = e(FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 1;
val it_advance_help_thm = MATCH_MP ((CONJUNCT2 (SPEC_ALL fix_flags_lem))) (GEN_ALL (top_thm()));
val _ = add_to_simplist it_advance_help_thm;
val IT_advance_empty_thm = prove_and_save(``IT_advance <|proc:=0|>``, "IT_advance_empty_thm");
val IT_advance_thm = save_thm("IT_advance_thm", MATCH_MP extras_lem2 (SPEC_ALL IT_advance_empty_thm));


(* set q  *)

val _ = g `!e. preserve_relation_mmu (set_q <|proc:=0|>) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = e(STRIP_TAC);
val _ = e(ASSUME_TAC (SPECL [``(set_q <|proc := 0|> ):(unit M)``, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``, ``empty_unt``, ``empty_sim``] (INST_TYPE [alpha |-> type_of(``()``)] fix_flags_lem)));
val _ = e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
val _ = e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
val _ = e(RW_TAC (srw_ss()) [set_q_def]);
val _ = e(ASSUME_TAC (SPECL [``(λcpsr. write_cpsr <|proc := 0|> (cpsr with Q := T)):(ARMpsr -> unit M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> type_of(``()``)] cpsr_simp_rel_ext_lem)));
val _ = e(FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 1;
val set_q_empty_thm = save_thm("set_q_empty_thm", top_thm());
val set_q_thm = save_thm("set_q_thm", MATCH_MP extras_lem2 (SPEC_ALL set_q_empty_thm));


(* read spsr *)


val _ = g `preserve_relation_mmu (read_spsr <|proc:=0|>) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = e(ASSUME_TAC (SPECL [``(read_spsr <|proc := 0|> ):(ARMpsr M)``, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``, ``empty_unt``, ``empty_sim``] (INST_TYPE [alpha |-> Type `:ARMpsr`] fix_flags_lem)));
val _ = e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
val _ = e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
val _ = e(RW_TAC (srw_ss()) [read_spsr_def]);
val _ = e(ASSUME_TAC (SPECL [``(λcpsr.
      bad_mode <|proc := 0|> cpsr.M >>=
      (λbad_mode.
         if bad_mode then
           errorT "read_spsr: unpredictable"
         else
           case cpsr.M of
             17w => read__psr <|proc := 0|> SPSR_fiq
           | 18w => read__psr <|proc := 0|> SPSR_irq
           | 19w => read__psr <|proc := 0|> SPSR_svc
           | 22w => read__psr <|proc := 0|> SPSR_mon
           | 23w => read__psr <|proc := 0|> SPSR_abt
           | 27w => read__psr <|proc := 0|> SPSR_und
           | cpsr.M => errorT "read_spsr: unpredictable")):(ARMpsr -> ARMpsr M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> Type `:ARMpsr`] cpsr_simp_rel_ext_lem)));
val _ = e(FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 1;
val read_spsr_empty_thm = save_thm("read_spsr_empty_thm", top_thm());
val read_spsr_thm = save_thm("read_spsr_thm", MATCH_MP extras_lem2 (SPEC_ALL read_spsr_empty_thm));


(* if-then *)
val _ = g ` preserve_relation_mmu
        (read_cpsr <|proc :=0|> >>=
         (\cpsr.
          (increment_pc <|proc :=0|> Encoding_Thumb |||
           write_cpsr <|proc :=0|> (cpsr with IT := (something))) >>= (λ(u1,u2). return ()))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim `;
val _ = e(ASSUME_TAC (SPECL [``(read_cpsr <|proc :=0|> >>=
         (\cpsr.
          (increment_pc <|proc :=0|> Encoding_Thumb |||
          write_cpsr <|proc :=0|> (cpsr with IT := (something))) >>= (λ(u1,u2). return ()))):(unit M)``, ``(assert_mode 16w: arm_state -> bool)``,  ``(assert_mode 16w: arm_state -> bool)``, ``empty_unt``, ``empty_sim``](INST_TYPE [alpha |-> type_of (``()``)] fix_flags_lem)));
val _ = e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
val _ = e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
val _ = e(RW_TAC (srw_ss()) []);
val _ = e(ASSUME_TAC (SPECL [``(\cpsr. (increment_pc <|proc := 0|> Encoding_Thumb
         ||| write_cpsr <|proc := 0|> (cpsr with IT := something)) >>=
            (λ(u1,u2). return ())):(ARMpsr -> unit M)``, ``(assert_mode 16w: arm_state -> bool)``, ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``](INST_TYPE [alpha |-> type_of (``()``)] cpsr_simp_rel_ext_lem)));
val _ = e (FULL_SIMP_TAC (srw_ss()) [parT_def]);
val _ = go_on 1;
val if_then_instr_help_lem1 = save_thm(
    "if_then_instr_help_lem1", MATCH_MP extras_lem2 (top_thm()));


val if_then_instr_help_lem2 = store_thm(
    "if_then_instr_hel_lem2",
    `` preserve_relation_mmu (read_cpsr <|proc :=0|> >>=
       (\cpsr.
          (increment_pc <|proc :=0|> Encoding_Thumb |||
           write_cpsr <|proc :=0|> (cpsr with IT := (firstcond @@ mask))) >>= (λ(u1,u2). return ()))) (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar``,
    ASSUME_TAC (SPECL [``xI:bool``, ``xF:bool``, ``(firstcond @@ mask):word8``] (GEN_ALL if_then_instr_help_lem1))
       THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_comb_16_27_thm]);
val _ = add_to_simplist if_then_instr_help_lem2;



val if_then_instr_comb_thm = prove_and_save_p (``if_then_instr <|proc:=0|> (If_Then firstcond mask)``, "if_then_instr_comb_thm", ``if_then_instr``);



(* check array *)

val _ = g` preserve_relation_mmu ((read_reg <|proc:=0|> 15w ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m |||
        read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>=
         (\(pc,rn,rm,cpsr,teehbr).
          if rn <=+ rm then
            ((write_reg <|proc:=0|> 14w ((0 :+ T) pc) |||
              write_cpsr <|proc:=0|> (cpsr with IT := 0w)) >>=
             ( \ (u1:unit,u2:unit).
               branch_write_pc <|proc:=0|> (teehbr + 0xFFFFFFF8w)))
          else
            increment_pc <|proc:=0|> Encoding_ThumbEE))(assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)`;
val _ = e(ASSUME_TAC (SPECL [``15w:word4``, ``n:word4``, ``m:word4``, ``(\(pc,rn,rm,cpsr,teehbr).
          if rn <=+ rm then
            ((write_reg <|proc:=0|> 14w ((0 :+ T) pc) |||
              write_cpsr <|proc:=0|> (cpsr with IT := 0w)) >>=
             ( \ (u1:unit,u2:unit).
               branch_write_pc <|proc:=0|> (teehbr + 0xFFFFFFF8w)))
          else
            increment_pc <|proc:=0|> Encoding_ThumbEE):(word32 # word32 # word32 # ARMpsr # word32 -> unit M)``, ``(assert_mode 16w: arm_state -> bool)`` ](INST_TYPE [alpha |-> type_of (``()``)] cpsr_quintuple_simp_rel_ext_lem)));
val _ = e (FULL_SIMP_TAC (srw_ss()) [parT_def]);
val _ = go_on 1;
val check_array_instr_help_lem1 = save_thm(
    "check_array_instr_help_lem1", (MATCH_MP extras_lem2 (MATCH_MP ((CONJUNCT2 (SPEC_ALL fix_flags_lem))) (GENL [``xI:bool``, ``xF:bool``] (top_thm())))));


val check_array_instr_help_lem2 = store_thm(
    "check_array_instr_help_lem2",
    `` preserve_relation_mmu ((read_reg <|proc:=0|> 15w ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m |||
        read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>=
         (\(pc,rn,rm,cpsr,teehbr).
          if rn <=+ rm then
            ((write_reg <|proc:=0|> 14w ((0 :+ T) pc) |||
              write_cpsr <|proc:=0|> (cpsr with IT := 0w)) >>=
             ( \ (u1:unit,u2:unit).
               branch_write_pc <|proc:=0|> (teehbr + 0xFFFFFFF8w)))
          else
            increment_pc <|proc:=0|> Encoding_ThumbEE))(assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar``,
    ASSUME_TAC check_array_instr_help_lem1
       THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_comb_16_27_thm]);
val _ = add_to_simplist check_array_instr_help_lem2;

val check_array_instr_comb_thm = prove_and_save_p (``check_array_instr <|proc:=0|> (Check_Array n m)``, "check_array_instr_comb_thm", ``check_array_instr``);


(* null check if thumbee *)

val _ = g `preserve_relation_mmu((read_reg <|proc:=0|> 15w ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>=
            (\(pc,cpsr,teehbr).
               (write_reg <|proc:=0|> 14w ((0 :+ T) pc) |||
                write_cpsr <|proc:=0|> (cpsr with IT := 0w)) >>=
               (\(u1:unit, u2:unit).
                 branch_write_pc <|proc:=0|> (teehbr  + 0xFFFFFFFCw))))(assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)`;
val _ = e(ASSUME_TAC (SPECL [`` (\(pc,cpsr,teehbr).
               (write_reg <|proc:=0|> 14w ((0 :+ T) pc) |||
                write_cpsr <|proc:=0|> (cpsr with IT := 0w)) >>=
               (\(u1:unit, u2:unit).
                 branch_write_pc <|proc:=0|> (teehbr  + 0xFFFFFFFCw))):(word32 # ARMpsr # word32 -> unit M)``, ``(assert_mode 16w: arm_state -> bool)``] (INST_TYPE [alpha |-> type_of (``()``)] cpsr_triple_simp_rel_ext_lem)));
val _ = e (FULL_SIMP_TAC (srw_ss()) [parT_def]);
val _ = go_on 1;
val null_check_if_thumbee_help_lem = (MATCH_MP extras_lem2 (MATCH_MP ((CONJUNCT2 (SPEC_ALL fix_flags_lem))) (GENL [``xI:bool``, ``xF:bool``] (top_thm()))));
val _ = add_to_simplist null_check_if_thumbee_help_lem;




(************************************************************)
(*******  D. taking privilege levels into account  **********)
(************************************************************)



val current_mode_is_user_or_system_eval_lem = store_thm(
    "current_mode_is_user_or_system_eval_lem",
    ``!s x s'.
     (assert_mode 16w s)      ==>
     (~ (access_violation s)) ==>
     (current_mode_is_user_or_system <|proc:=0|> s = ValueState x s')
        ==> x``,
    EVAL_TAC THEN RW_TAC (srw_ss()) []);

val current_mode_is_user_or_system_eval_lem2 = store_thm(
    "current_mode_is_user_or_system_eval_lem2",
    ``!s x s'.
     (assert_mode 16w s)      ==>
     (current_mode_is_user_or_system <|proc:=0|> s = ValueState x s') ==>
     (~ (access_violation s'))
        ==> x``,
    EVAL_TAC
      THEN REPEAT STRIP_TAC
      THEN Cases_on `access_violation s` THEN FULL_SIMP_TAC (srw_ss()) []
      THENL [METIS_TAC [], UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []]);


val priv_simp_lem = store_thm(
    "priv_simp_lem",
    ``!s ifcomp elsecomp.
      (assert_mode 16w s) ==>
      (((current_mode_is_priviledged <|proc:=0|> >>=
       (\current_mode_is_priviledged.
           if current_mode_is_priviledged then
             ifcomp
           else
             elsecomp)) s)
      =
      ((current_mode_is_priviledged <|proc:=0|> >>=
       (\current_mode_is_priviledged.
           elsecomp)) s))``,
     EVAL_TAC THEN RW_TAC (srw_ss()) []);


val user_simp_lem = store_thm(
    "user_simp_lem",
    ``!s E elsecomp.
      (assert_mode 16w s) ==>
      (((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                if is_user_or_system_mode then
                  errorT E
                else
                  elsecomp)) s)
      =
      ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                errorT E)) s))``,
    EVAL_TAC THEN RW_TAC (srw_ss()) []);

val user_simp_or_lem = store_thm(
    "user_simp_or_lem",
    ``!s E A elsecomp.
      (assert_mode 16w s) ==>
      (((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                if is_user_or_system_mode \/ A then
                  errorT E
                else
                  elsecomp)) s)
      =
      ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                errorT E)) s))``,
    EVAL_TAC THEN RW_TAC (srw_ss()) []);


val user_simp_par_or_lem = store_thm(
    "user_simp_par_or_lem",
    ``!s E A P elsecomp.
      (assert_mode 16w s) ==>
      ((((current_mode_is_user_or_system <|proc := 0|> ||| P)>>=
             (λ(is_user_or_system_mode,otherparam).
                if is_user_or_system_mode \/ A then
                  errorT E
                else
                  elsecomp)) s)
      =
      (((current_mode_is_user_or_system <|proc := 0|> ||| P )>>=
             (λ(is_user_or_system_mode,otherparam).
                errorT E)) s))``,
    EVAL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN Cases_on `P s`
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN Cases_on `access_violation b`
       THEN FULL_SIMP_TAC (srw_ss()) []);




val user_simp_par_or_and_lem = store_thm(
    "user_simp_par_or_and_lem",
    ``!s E A P elsecomp.
      (assert_mode 16w s) ==>
      ((((current_mode_is_user_or_system <|proc := 0|> ||| P)>>=
             (λ(is_user_or_system_mode,otherparam).
                if is_user_or_system_mode \/ (A /\ otherparam) then
                  errorT E
                else
                  elsecomp)) s)
      =
      (((current_mode_is_user_or_system <|proc := 0|> ||| P )>>=
             (λ(is_user_or_system_mode,otherparam).
                errorT E)) s))``,
    EVAL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN Cases_on `P s`
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN Cases_on `access_violation b`
       THEN FULL_SIMP_TAC (srw_ss()) []);


val user_simp_par_or_eqv_lem = store_thm(
    "user_simp_par_or_eqv_lem",
    ``!s E x P elsecomp.
      (assert_mode 16w s) ==>
      ((((current_mode_is_user_or_system <|proc := 0|> ||| P)>>=
             (λ(is_user_or_system_mode,otherparam).
                if is_user_or_system_mode \/ (otherparam = x) then
                  errorT E
                else
                  elsecomp)) s)
      =
      (((current_mode_is_user_or_system <|proc := 0|> ||| P )>>=
             (λ(is_user_or_system_mode,otherparam).
                errorT E)) s))``,
    EVAL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN Cases_on `P s`
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN Cases_on `access_violation b`
       THEN FULL_SIMP_TAC (srw_ss()) []);



val priv_simp_rel_lem = store_thm(
    "priv_simp_rel_lem",
    ``!ifcomp elsecomp inv2 uf uy.
      (preserve_relation_mmu
        (current_mode_is_priviledged <|proc:=0|> >>=
          (\current_mode_is_priviledged.
           if current_mode_is_priviledged then
             ifcomp
           else
             elsecomp)) (assert_mode 16w) (inv2) uf uy)
        =
      (preserve_relation_mmu
       (current_mode_is_priviledged <|proc:=0|> >>=
          (\current_mode_is_priviledged.
             elsecomp)) (assert_mode 16w) (inv2) uf uy)``,
     RW_TAC (srw_ss()) [priv_simp_lem, preserve_relation_mmu_def]);



val user_simp_rel_lem = store_thm(
    "user_simp_rel_lem",
    ``!E elsecomp uf uy.
      (preserve_relation_mmu
       ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                if is_user_or_system_mode then
                  (errorT E: 'a M)
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) uf uy)
        =
      (preserve_relation_mmu
       ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                (errorT E: 'a M)))) (assert_mode 16w) (assert_mode 16w) uf uy)``,
     RW_TAC (srw_ss()) [user_simp_lem, preserve_relation_mmu_def]);


val user_simp_or_rel_lem = store_thm(
    "user_simp_or_rel_lem",
    ``!E A elsecomp uf uy.
      (preserve_relation_mmu
       ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                if is_user_or_system_mode \/ A then
                  (errorT E: 'a M)
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) uf uy)
        =
      (preserve_relation_mmu
       ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                (errorT E: 'a M)))) (assert_mode 16w) (assert_mode 16w) uf uy)``,
     RW_TAC (srw_ss()) [user_simp_or_lem, preserve_relation_mmu_def]);


val user_simp_par_or_rel_lem = store_thm(
    "user_simp_par_or_rel_lem",
    ``!E A (P:'b M) elsecomp uf uy.
      (preserve_relation_mmu
       (((current_mode_is_user_or_system <|proc := 0|> ||| P) >>=
             (λ(is_user_or_system_mode,otherparam).
                if is_user_or_system_mode \/ A then
                  (errorT E: 'a M)
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) uf uy)
        =
      (preserve_relation_mmu
       (((current_mode_is_user_or_system <|proc := 0|> ||| P)>>=
             (λ(is_user_or_system_mode,otherparam).
                (errorT E: 'a M)))) (assert_mode 16w) (assert_mode 16w) uf uy)``,
     RW_TAC (srw_ss()) [user_simp_par_or_lem, preserve_relation_mmu_def]);


val user_simp_par_or_eqv_rel_lem = store_thm(
    "user_simp_par_or_eqv_rel_lem",
    ``!E x (P:'b M) elsecomp uf uy.
      (preserve_relation_mmu
       (((current_mode_is_user_or_system <|proc := 0|> ||| P) >>=
             (λ(is_user_or_system_mode,otherparam).
                if is_user_or_system_mode \/ (otherparam = x) then
                  (errorT E: 'a M)
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) uf uy)
        =
      (preserve_relation_mmu
       (((current_mode_is_user_or_system <|proc := 0|> ||| P)>>=
             (λ(is_user_or_system_mode,otherparam).
                (errorT E: 'a M)))) (assert_mode 16w) (assert_mode 16w) uf uy)``,
    RW_TAC (srw_ss()) [user_simp_par_or_eqv_lem, preserve_relation_mmu_def]);


val user_simp_par_or_and_rel_lem = store_thm(
    "user_simp_par_or_and_rel_lem",
    ``!E A P elsecomp uf uy.
      (preserve_relation_mmu
       (((current_mode_is_user_or_system <|proc := 0|> ||| P) >>=
             (λ(is_user_or_system_mode,otherparam).
                if is_user_or_system_mode \/ (A /\ otherparam) then
                  (errorT E: 'a M)
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) uf uy)
        =
      (preserve_relation_mmu
       (((current_mode_is_user_or_system <|proc := 0|> ||| P)>>=
             (λ(is_user_or_system_mode,otherparam).
                (errorT E: 'a M)))) (assert_mode 16w) (assert_mode 16w) uf uy)``,
     RW_TAC (srw_ss()) [user_simp_par_or_and_lem, preserve_relation_mmu_def]);



val priv_simp_preserves_help_comb_thm = prove_and_save_p_helper (``current_mode_is_priviledged <|proc := 0|> >>=
            (\current_mode_is_priviledged. take_undef_instr_exception <|proc:=0|>)``, "priv_simp_preserves_comb_help_thm");

val user_simp_preserves_help_thm = prove_and_save (``current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode. (errorT E))``, "user_simp_preserves_help_thm");



val priv_simp_preserves_comb_thm = store_thm(
    "priv_simp_preserves_comb_thm",
    ``!ifcomp.
      (preserve_relation_mmu
        (current_mode_is_priviledged <|proc:=0|> >>=
          (\current_mode_is_priviledged.
           if current_mode_is_priviledged then
             ifcomp
           else
             take_undef_instr_exception <|proc:=0|>)) (assert_mode 16w) (comb_mode 16w 27w)  priv_mode_constraints priv_mode_similar)``,
     RW_TAC (srw_ss()) [priv_simp_rel_lem, priv_simp_preserves_help_comb_thm]);



val user_simp_preserves_empty_thm = store_thm(
    "user_simp_preserves_empty_thm",
    ``!E elsecomp. (preserve_relation_mmu
       ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                if is_user_or_system_mode then
                  errorT E
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim)``,
     RW_TAC (srw_ss()) [user_simp_rel_lem, user_simp_preserves_help_thm]);

val user_simp_preserves_thm = (MATCH_MP extras_lem2 (SPEC_ALL user_simp_preserves_empty_thm));

val user_simp_or_preserves_empty_thm = store_thm(
    "user_simp_or_preserves_empty_thm",
    ``!E A elsecomp. (preserve_relation_mmu
       ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                if is_user_or_system_mode \/ A then
                  errorT E
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim)``,
     RW_TAC (srw_ss()) [user_simp_or_rel_lem, user_simp_preserves_help_thm]);

val user_simp_or_preserves_thm = (MATCH_MP extras_lem2 (SPEC_ALL user_simp_or_preserves_empty_thm));


val _ = add_to_simplist user_simp_preserves_thm;
val _ = add_to_simplist user_simp_or_preserves_thm;
val _ = add_to_simplist priv_simp_preserves_comb_thm;



(************************************************************)
(*********************  E. Coprocessors   *******************)
(************************************************************)



val coproc_accepted_ax =  new_axiom("coproc_accepted_ax",
                          ``!s s' inst accept. (assert_mode 16w s) ==> (coproc_accepted <|proc:=0|> inst s = ValueState accept s') ==> (~accept)``);


val coproc_accepted_constlem = store_thm(
    "coproc_accepted_constlem",
    ``!s inst. ?x. coproc_accepted <|proc:=0|> inst s = ValueState x s``,
    REPEAT STRIP_TAC THEN EVAL_TAC THEN RW_TAC (srw_ss()) [])


val coproc_accepted_usr_def = store_thm(
    "coproc_accepted_usr_def",
    ``!s inst. (assert_mode 16w s) ==> (coproc_accepted <|proc:=0|> inst s = ValueState F s)``,
    RW_TAC (srw_ss()) []
       THEN Cases_on `coproc_accepted <|proc := 0|> inst s`
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN IMP_RES_TAC coproc_accepted_ax
       THEN ASSUME_TAC (SPECL [``s:arm_state``, ``inst:CPinstruction``] coproc_accepted_constlem)
       THEN (NTAC 2 (FULL_SIMP_TAC (srw_ss()) [])));


val coproc_accepted_empty_thm = store_thm(
    "coproc_accepted_empty_thm",
    ``!inst. preserve_relation_mmu (coproc_accepted <|proc:=0|> inst) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [coproc_accepted_usr_def, preserve_relation_mmu_def, untouched_def, empty_unt_def, empty_sim_def] THEN RW_TAC (srw_ss()) []);

val coproc_accepted_thm = save_thm("coproc_accepted_thm", (MATCH_MP extras_lem2 (SPEC_ALL coproc_accepted_empty_thm)));


val coproc_accepted_simp_lem = store_thm(
    "coproc_accepted_simp_lem",
    ``!s inst ifcomp elsecomp.
        (assert_mode 16w s) ==>
        ((coproc_accepted <|proc:=0|> inst >>=
                (λaccepted.
                   if ¬accepted then
                     ifcomp
                   else
                     elsecomp)) s
         =
         (coproc_accepted <|proc:=0|> inst >>=
                (λaccepted.ifcomp)) s)``,
     REPEAT STRIP_TAC
        THEN FULL_SIMP_TAC (srw_ss()) [seqT_def]
        THEN Cases_on `coproc_accepted <|proc := 0|> inst s`
        THEN IMP_RES_TAC coproc_accepted_ax
        THEN FULL_SIMP_TAC (srw_ss()) []);


val coproc_accepted_simp_rel_lem = store_thm(
    "coproc_accepted_simp_rel_lem",
    ``!coproc ThisInstr ifcomp elsecomp inv2 uf uy.
      (preserve_relation_mmu
        (coproc_accepted <|proc:=0|> (coproc,ThisInstr) >>=
                (λaccepted.
                   if ¬accepted then
                     ifcomp
                   else
                     elsecomp)) (assert_mode 16w) (inv2) uf uy)
        =
      (preserve_relation_mmu
        (coproc_accepted <|proc:=0|> (coproc,ThisInstr) >>=
                (λaccepted. ifcomp)) (assert_mode 16w) (inv2) uf uy)``,
     RW_TAC (srw_ss()) [coproc_accepted_simp_lem, preserve_relation_mmu_def]);



val coproc_accepted_simp_preserves_help_comb_thm = prove_and_save_p_helper (``coproc_accepted <|proc := 0|> (coproc,ThisInstr) >>=
            (\accepted. take_undef_instr_exception <|proc:=0|>)``, "coproc_accepted_simp_preserves_comb_help_thm");



val coproc_accepted_simp_preserves_comb_thm = store_thm(
    "coproc_accepted_simp_preserves_comb_thm",
    ``!coproc ThisInstr elsecomp.
      preserve_relation_mmu
        (coproc_accepted <|proc:=0|> (coproc,ThisInstr) >>=
                (λaccepted.
                   if ¬accepted then
                     take_undef_instr_exception <|proc:=0|>
                   else
                     elsecomp)) (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints
     priv_mode_similar``,
     RW_TAC (srw_ss()) [coproc_accepted_simp_rel_lem, coproc_accepted_simp_preserves_help_comb_thm]);


val _ = add_to_simplist coproc_accepted_simp_preserves_comb_thm;



(************************************************************)
(******** F. Once again PSRs: *psr_write_by_instr   *********)
(************************************************************)



(* cpsr_write_by_instr *)


val cpsr_write_by_instr_part1 =
``(λ(priviledged,is_secure,nsacr,badmode).
    if
      (bytemask:word4) ' 0 ∧ priviledged ∧
      (badmode ∨ ¬is_secure ∧ ((((4 >< 0) (value:word32)):word5)= 22w) ∨
       ¬is_secure ∧ ((((4 >< 0) value):word5) = 17w) ∧ nsacr.RFR)
    then
      errorT "cpsr_write_by_instr: unpredictable"
    else
      (read_sctlr <|proc := 0|> ||| read_scr <|proc := 0|>
         ||| read_cpsr <|proc := 0|>) >>=
      (λ(sctlr,scr,cpsr).
         write_cpsr <|proc := 0|>
           (cpsr with
            <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
              Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
              C := if bytemask ' 3 then value ' 29 else cpsr.C;
              V := if bytemask ' 3 then value ' 28 else cpsr.V;
              Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
              IT :=
                if affect_execstate then
                  if bytemask ' 3 then
                    if bytemask ' 1 then
                        (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                  else
                    cpsr.IT
                else
                  cpsr.IT;
              J :=  if bytemask ' 3 ∧ affect_execstate then value ' 24  else cpsr.J;
              GE := if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
              E := if bytemask ' 1 then value ' 9 else cpsr.E;
              A :=  if  bytemask ' 1 ∧ priviledged ∧ (is_secure ∨ scr.AW) then  value ' 8 else  cpsr.A;
              I :=  if bytemask ' 0 ∧ priviledged then value ' 7 else cpsr.I;
              F :=  if bytemask ' 0 ∧ priviledged ∧ (is_secure ∨ scr.FW) /\ (¬sctlr.NMFI ∨ ¬value ' 6) then value ' 6 else cpsr.F;
              T := if bytemask ' 0 ∧ affect_execstate then value ' 5 else cpsr.T;
              M := if bytemask ' 0 ∧ priviledged then (4 >< 0) value else cpsr.M|>)))
       :(bool # bool # CP15nsacr # bool -> unit M)``;


val cpsr_write_by_instr_part2 =
``(λ(sctlr,scr,cpsr).
             write_cpsr <|proc := 0|>
               (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=
                    if bytemask ' 3 ∧ affect_execstate then
                      value ' 24
                    else
                      cpsr.J;
                  GE :=
                    if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A; I := cpsr.I; F := cpsr.F;
                  T :=
                    if bytemask ' 0 ∧ affect_execstate then
                      value ' 5
                    else
                      cpsr.T; M := cpsr.M|>))
          :(CP15sctlr # CP15scr # ARMpsr -> unit M)``;

val cpsr_write_by_instr_components_without_mode = `` (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=  if bytemask ' 3 ∧ affect_execstate then value ' 24 else cpsr.J;
                  GE := if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A; I := cpsr.I; F := cpsr.F;
                  T :=  if bytemask ' 0 ∧ affect_execstate then value ' 5 else cpsr.T|>)``;

val cpsr_write_by_instr_components_without_IFM = `` (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=  if bytemask ' 3 ∧ affect_execstate then value ' 24 else cpsr.J;
                  GE := if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A;
                  T :=  if bytemask ' 0 ∧ affect_execstate then value ' 5 else cpsr.T|>)``;


val cpsr_write_by_instr_components_with_mode = `` (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=  if bytemask ' 3 ∧ affect_execstate then value ' 24 else cpsr.J;
                  GE := if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A; I := cpsr.I; F := cpsr.F;
                  T :=  if bytemask ' 0 ∧ affect_execstate then value ' 5 else cpsr.T;
                  M := 16w|>)``;


val cpsr_write_by_instr_components_complete = `` (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=  if bytemask ' 3 ∧ affect_execstate then value ' 24 else cpsr.J;
                  GE := if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A; I := xI; F := xF;
                  T :=  if bytemask ' 0 ∧ affect_execstate then value ' 5 else cpsr.T;
                  M := 16w|>)``;


val cpsr_write_by_instr_unpriv_def = Define `cpsr_write_by_instr_unpriv (value:word32, bytemask:word4, affect_execstate:bool) = ((current_mode_is_priviledged <|proc := 0|>
          ||| is_secure <|proc := 0|> ||| read_nsacr <|proc := 0|>
          ||| bad_mode <|proc := 0|> ((4 >< 0) value)) >>=
       (λ(p,s,n,b).
          (read_sctlr <|proc := 0|> ||| read_scr <|proc := 0|>
             ||| read_cpsr <|proc := 0|>) >>=
          (λ(sctlr,scr,cpsr).
             write_cpsr <|proc := 0|>
               (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=
                    if bytemask ' 3 ∧ affect_execstate then
                      value ' 24
                    else
                      cpsr.J;
                  GE :=
                    if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A; I := cpsr.I; F := cpsr.F;
                  T :=
                    if bytemask ' 0 ∧ affect_execstate then
                      value ' 5
                    else
                      cpsr.T; M := cpsr.M|>))))`;



val priv_simp_lem2 = store_thm(
    "priv_simp_lem2",
    ``!s x H . (assert_mode 16w s) ==>
       ((((current_mode_is_priviledged <|proc:=0|> ||| is_secure <|proc:=0|> ||| read_nsacr <|proc:=0|> ||| bad_mode <|proc:=0|> x) >>= (\ (p,s,n,b). H (p,s,n,b))) s)
      = (((current_mode_is_priviledged <|proc:=0|> ||| is_secure <|proc:=0|> ||| read_nsacr <|proc:=0|> ||| bad_mode <|proc:=0|> x) >>= (\ (p,s,n,b). H (F,s,n,b))) s))``,
    EVAL_TAC THEN RW_TAC (srw_ss()) []);


val cpsr_write_by_instr_simp_lem = store_thm(
    "cpsr_write_by_instr_simp_lem",
    ``!s value bytemask affect_execstate. (assert_mode 16w s) ==>
      (cpsr_write_by_instr <|proc:=0|> (value,bytemask,affect_execstate) s
     = cpsr_write_by_instr_unpriv (value,bytemask,affect_execstate) s)``,
    RW_TAC (srw_ss()) [cpsr_write_by_instr, cpsr_write_by_instr_unpriv_def]
       THEN IMP_RES_TAC (SPECL [``s:arm_state``, ``((4 >< 0)(value:word32)):word5``, cpsr_write_by_instr_part1] (INST_TYPE [alpha |-> (type_of(``()``))] priv_simp_lem2))
       THEN FULL_SIMP_TAC (srw_ss()) []);


val cpsr_write_by_instr_simp_rel_lem = store_thm(
    "cpsr_write_by_instr_simp_rel_lem",
    ``!value bytemask affect_execstate uf uy.
      (preserve_relation_mmu (cpsr_write_by_instr <|proc:=0|> (value,bytemask,affect_execstate)) (assert_mode 16w) (assert_mode 16w) uf uy)
     = (preserve_relation_mmu (cpsr_write_by_instr_unpriv (value,bytemask,affect_execstate)) (assert_mode 16w) (assert_mode 16w) uf uy)``,
    RW_TAC (srw_ss()) [cpsr_write_by_instr_simp_lem, preserve_relation_mmu_def]);


val _ = g `preserve_relation_mmu
  (write_cpsr <|proc := 0|> (^cpsr_write_by_instr_components_complete)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)`;
val _ = e (Q.ABBREV_TAC `cpsr2 = ^cpsr_write_by_instr_components_without_IFM`);
val _ = e(`^cpsr_write_by_instr_components_complete = (cpsr2) with <|I:= xI; F:= xF; M := 16w|>` by Q.UNABBREV_TAC `cpsr2` THEN FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 1;
val write_cpsr_by_instruction_all_components_thm = save_thm(
   "write_cpsr_by_instruction_all_components_thm", top_thm());
val _ = add_to_simplist (write_cpsr_by_instruction_all_components_thm);


val _ = g `(preserve_relation_mmu ((read_sctlr <|proc := 0|> ||| read_scr <|proc := 0|>
             ||| read_cpsr <|proc := 0|>) >>=
          (λ (sctlr,scr,cpsr).
             write_cpsr <|proc := 0|>
               (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=  if bytemask ' 3 ∧ affect_execstate then value ' 24 else cpsr.J;
                  GE := if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A; I := cpsr.I; F := cpsr.F;
                  T :=  if bytemask ' 0 ∧ affect_execstate then value ' 5 else cpsr.T;
                  M := cpsr.M|>))) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim))`;
val _ = e(ASSUME_TAC (SPECL [cpsr_write_by_instr_part2, ``(assert_mode 16w: arm_state -> bool)``] (INST_TYPE [alpha |-> type_of (``()``)] cpsr_triple_simp_rel_ext_lem2)));
val _ = e (FULL_SIMP_TAC (srw_ss()) []);
val _ = go_on 1;
val write_cpsr_by_instruction_help_lem = save_thm(
   "write_cpsr_by_instruction_help_lem", top_thm());
val _ = add_to_simplist write_cpsr_by_instruction_help_lem;


val _ = g `(preserve_relation_mmu (cpsr_write_by_instr <|proc:=0|> (value,bytemask,affect_execstate)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim))`;
val _ = e (FULL_SIMP_TAC (srw_ss()) [cpsr_write_by_instr_simp_rel_lem, cpsr_write_by_instr_unpriv_def]);
val _ = go_on 1;
val cpsr_write_by_instr_thm = save_thm("cpsr_write_by_instr_thm", (MATCH_MP extras_lem2 (MATCH_MP ((CONJUNCT2 (SPEC_ALL fix_flags_lem))) (GENL [``xI:bool``, ``xF:bool``] (top_thm())))));



(* spsr_write_by_instr *)


val _ = g `preserve_relation_mmu (spsr_write_by_instr <|proc:=0|> (vl, bm)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
val _ = e(FULL_SIMP_TAC (srw_ss()) [user_simp_par_or_and_rel_lem, spsr_write_by_instr_def]);
val _ = go_on 1;
val spsr_write_by_instr_thm = save_thm ("spsr_write_by_instr_thm", (MATCH_MP extras_lem2 (top_thm())));



(*****************************************************************)
(****  G. Common operations that are provable automatically  *****)
(*****************************************************************)


val increment_pc_thm = prove_and_save_e (``increment_pc <|proc:=0|> enc``, "increment_pc_thm");


val load_write_pc_thm = prove_and_save_e (``load_write_pc <|proc:=0|> addr``, "load_write_pc_thm");

val alu_write_pc_thm = prove_and_save_e (``alu_write_pc <|proc:=0|> addr``, "alu_write_pc_thm");

val arm_expand_imm_thm = prove_and_save_e (``arm_expand_imm <|proc:=0|> imm12``, "arm_expand_imm_thm");

val shift_thm = prove_and_save_e (``shift (value, type, amount, carry_in)``, "shift_thm");

val read_flags_thm = prove_and_save_e (``read_flags <|proc:=0|>``, "read_flags_thm");


val read_memU_thm = prove_and_save_e (``read_memU <|proc:=0|> (addr, n)``, "read_memU_thm");

val read_memU_unpriv_thm = prove_and_save_e (``read_memU_unpriv <|proc:=0|> (addr, n)``, "read_memU_unpriv_thm");

val read_memA_thm = prove_and_save_s (``read_memA <|proc:=0|> (addr, n)``, "read_memA_thm");

val write_memU_thm = prove_and_save_e (``write_memU <|proc:=0|> (addr, n) x``, "write_memU_thm");

val write_memU_unpriv_thm = prove_and_save_e (``write_memU_unpriv <|proc:=0|> (addr, n) x``, "write_memU_unpriv_thm");

val write_memA_thm = prove_and_save_e (``write_memA <|proc:=0|> (addr, n) x``, "write_memA_thm");

val read_reg_literal_thm = prove_and_save_e (``read_reg_literal <|proc:=0|> n``, "read_reg_literal_thm");

val big_endian_thm = prove_and_save_s (``big_endian <|proc:=0|>``, "big_endian_thm");

val unaligned_support_thm = prove_and_save_e (``unaligned_support <|proc:=0|>``, "unaligned_support_thm");

val pc_store_value_thm = prove_and_save_e (``pc_store_value <|proc:=0|>``, "pc_store_value_thm");

val is_secure_thm = prove_and_save_e(``is_secure <|proc:=0|>``, "is_secure_thm");

val read_nsacr_thm = prove_and_save_e(``read_nsacr <|proc:=0|>``, "read_nsacr_thm");

val current_instr_set_thm = prove_and_save_s(``current_instr_set <|proc:=0|>``, "current_instr_set_thm");

val branch_write_pc_thm = prove_and_save_e(``branch_write_pc <|proc:=0|> d``, "branch_write_pc_thm");

val no_operation_instr_comb_thm = prove_and_save_p (``no_operation_instr <|proc := 0|> enc``, "no_operation_instr_comb_thm", ``no_operation_instr``);


val simplist_export_thm = save_thm(
    "simplist_export_thm",
    LIST_CONJ (!simp_thms_list));



val _ = export_theory();
