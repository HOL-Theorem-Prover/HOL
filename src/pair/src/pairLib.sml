(*---------------------------------------------------------------------------*
 * Theory of pairs and associated support.                                   *
 *---------------------------------------------------------------------------*)

structure pairLib :> pairLib =
struct

local open pairTheory pairSimps pairTools PairRules in end;

open pairSyntax PairedLambda pairTools

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

end;
