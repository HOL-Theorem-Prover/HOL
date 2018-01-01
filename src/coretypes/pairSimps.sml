structure pairSimps :> pairSimps =
struct

open Lib Parse simpLib pairTheory PairedLambda;


(*------------------------------------------------------------------------*)
(* PAIR_ss                                                                *)
(*------------------------------------------------------------------------*)

val PAIR0_ss =
    SSFRAG
      {name=SOME"PAIR", convs=[],
      rewrs = pairTheory.pair_rws @
              [CLOSED_PAIR_EQ, CURRY_UNCURRY_THM, UNCURRY_CURRY_THM,
               CURRY_ONE_ONE_THM, UNCURRY_ONE_ONE_THM,CURRY_DEF,
               PAIR_MAP_THM, UNCURRY_DEF],
              filter=NONE,ac=[],dprocs=[],congs=[]}

val PAIR_ss = PAIR0_ss

val _ = BasicProvers.augment_srw_ss [PAIR_ss];


val fvar = ``f:'a -> 'b -> bool``;
val paired_forall_ss =
    conv_ss
      {name  = "ELIM_TUPLED_QUANT_CONV (remove paired quantification)",
       trace = 2,
       key   = SOME ([],``$! (UNCURRY ^fvar)``),
       conv  = K (K pairTools.ELIM_TUPLED_QUANT_CONV)}

val paired_exists_ss =
    conv_ss
      {name  = "ELIM_TUPLED_QUANT_CONV (remove paired quantification)",
       trace = 2,
       key   = SOME ([],``$? (UNCURRY ^fvar)``),
       conv  = K (K pairTools.ELIM_TUPLED_QUANT_CONV)}

val gen_beta_ss =
    conv_ss
      {name  = "GEN_BETA_CONV",
       trace = 2,
       key   = SOME ([],``(UNCURRY ^fvar) x``),
       conv  = K (K PairedLambda.GEN_BETA_CONV)}



end (* struct *)
