open HolKernel boolLib bossLib Parse
open termTheory nomsetTheory

val _ = new_theory "precn" (* "parameter recursion" *)

val lemma1 = prove(
  ``tpm [(x,y)] (if s1:string = s2 then t1 else t2) =
    if s1 = s2 then tpm [(x,y)] t1 else tpm [(x,y)] t2``,
  SRW_TAC [][]);

tm_recursion |> SIMP_RULE (srw_ss()) [FUN_EQ_THM, fnpm_def, support_def]

val precn0 =
    tm_recursion
        |> SPEC_ALL
        |> Q.INST_TYPE [`:'a` |-> `:term -> term`]
        |> Q.INST [`vr` |-> `λs e. if s = v then e else VAR s`,
                   `ap` |-> `λt1 t2 e. t1 e @@ t2 e`,
                   `lm` |-> `λy t e. fresh tpm
                                      (λy'. fnpm tpm tpm [(y,y')] t (x2 @@ e))`,
                   `A` |-> `v INSERT FV x2`,
                   `apm` |-> `fnpm tpm tpm`]
        |> SIMP_RULE (srw_ss()) []
        |> SIMP_RULE (srw_ss()) [support_def, FUN_EQ_THM, fnpm_def, lemma1,
                                 basic_swapTheory.swapstr_eq_left]
                                 GSYM tpm_APPEND]



val _ = export_theory()


