structure sumSimps :> sumSimps =
struct

open sumTheory;

val SUM_ss = simpLib.rewrites 
  [ISL,ISR,OUTL,OUTR,INL,INR,
   sum_distinct,Conv.GSYM sum_distinct,INR_INL_11,sum_case_def];


end (* struct *)
