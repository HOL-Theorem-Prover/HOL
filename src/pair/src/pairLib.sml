(*---------------------------------------------------------------------------*
 * Theory of pairs and associated support. This is currently somewhat        *
 * underpowered from Jim Grundy's implementation of the library, but offers  *
 * expanded syntax support.                                                  *
 *---------------------------------------------------------------------------*)

structure pairLib :> pairLib =
struct

local open pairTheory PairedDefinition pairSimps pairTools in end;

open pairSyntax PairedLambda 

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;


(*  
    open Pair_basic Pair_both1 Pair_forall Pair_exists Pair_both2 Pair_conv

    val _ = Lib.cons_path (!Globals.HOLdir^"library/pair/help/defs/") 

end;
