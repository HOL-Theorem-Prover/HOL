(*---------------------------------------------------------------------------*
 * Theory of pairs and associated support.                                   *
 *---------------------------------------------------------------------------*)

structure pairLib :> pairLib =
struct

local open pairTheory pairSimps pairTools PairRules in end;

open boolLib pairSyntax PairedLambda pairTools simpLib;

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

end
