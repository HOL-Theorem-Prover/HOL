structure sumSimps :> sumSimps =
struct

open sumTheory;

(* Note: OUTL (INR x) is not defined *)
val compute_thms =
  [ ISL,ISR,OUTL,OUTR,
    sum_distinct,Conv.GSYM sum_distinct,INR_INL_11,sum_case_def];

val SUM_ss = sum_rwts

val SUM_rws =
  computeLib.add_thms (List.map computeLib.lazyfy_thm compute_thms);

end (* struct *)
