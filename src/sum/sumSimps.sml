structure sumSimps :> sumSimps =
struct

open HolKernel basicHol90Lib ConstrProofs simpLib;

(* ---------------------------------------------------------------------
 * sum_ss
 * --------------------------------------------------------------------*)

val SUM_ss =
    let val s_axiom = sumTheory.sum_Axiom
        val s_distinct = prove_constructors_distinct s_axiom
        val s_d2 = ONCE_REWRITE_RULE [EQ_SYM_EQ] s_distinct
    in rewrites ([sumTheory.ISL,sumTheory.ISR,sumTheory.OUTL,
                 sumTheory.OUTR,sumTheory.INL,sumTheory.INR] @
		 [prove_constructors_one_one s_axiom, s_distinct, s_d2])
    end;


end (* struct *)
