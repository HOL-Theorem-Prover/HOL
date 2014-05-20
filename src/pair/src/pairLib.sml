(*---------------------------------------------------------------------------*
 * Theory of pairs and associated support.                                   *
 *---------------------------------------------------------------------------*)

structure pairLib :> pairLib =
struct

local open pairTheory pairSimps pairTools PairRules in end;

open boolLib pairSyntax PairedLambda pairTools simpLib;

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

val add_pair_compset = computeLib.add_thms
  (List.map computeLib.lazyfy_thm
     let open pairTheory in
       [CLOSED_PAIR_EQ,FST,SND,pair_case_thm,SWAP_def,
        CURRY_DEF,UNCURRY_DEF,PAIR_MAP_THM]
     end)

val () = add_pair_compset computeLib.the_compset

end
