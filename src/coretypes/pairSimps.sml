structure pairSimps :> pairSimps =
struct

open Lib Parse simpLib pairTheory PairedLambda;


val PAIR_ss = BasicProvers.thy_ssfrag "pair"

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
