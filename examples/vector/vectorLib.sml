structure vectorLib :> vectorLib =
struct

open HolKernel Parse boolLib bossLib;

open pred_setTheory realTheory realLib iterateTheory RealArith fcpTheory fcpLib
     tautLib vectorTheory real_sigmaTheory;

(* tactics and decision procedures *)

val VECTOR_ARITH_TAC =
    rpt GEN_TAC
 >> SIMP_TAC std_ss [dot_def, GSYM SUM_ADD', GSYM SUM_SUB', FINITE_COUNT,
                     GSYM SUM_LMUL, GSYM SUM_RMUL, GSYM SUM_NEG']
 >> (MATCH_MP_TAC SUM_EQ ORELSE MATCH_MP_TAC SUM_EQ_0' ORELSE
     GEN_REWRITE_TAC ONCE_DEPTH_CONV empty_rewrites [CART_EQ])
 >> SIMP_TAC bool_ss[GSYM FORALL_AND_THM] >> TRY EQ_TAC
 >> TRY(HO_MATCH_MP_TAC MONO_ALL) >> TRY GEN_TAC
 >> REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`,
                TAUT `(a ==> b) \/ (a ==> c) <=> a ==> b \/ c`]
 >> TRY (MATCH_MP_TAC(TAUT `(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)`))
 >> SRW_TAC[FCP_ss][vector_add_def, vector_sub_def, vector_neg_def,
                    vector_mul_def, vec_def]
 >> TRY (POP_ASSUM MP_TAC)
 >> REAL_ARITH_TAC;

fun VECTOR_ARITH tm = prove(tm,VECTOR_ARITH_TAC);

end; (* structure *)
