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

end (* struct *)
