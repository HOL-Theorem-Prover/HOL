(*---------------------------------------------------------------------------*
 * Theory of pairs and associated support. This is currently somewhat        *
 * underpowered from Jim Grundy's implementation of the library, but offers  *
 * expanded syntax support.                                                  *
 *---------------------------------------------------------------------------*)

structure pairLib :> pairLib =
struct

local open pairTheory pairSimps pairTools in end;

open pairSyntax PairedLambda 

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

end;
