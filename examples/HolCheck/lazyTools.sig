signature lazyTools =
sig
    val mk_lthm : (unit -> Term.term * (unit -> Thm.thm)) -> (unit -> Thm.thm) -> Thm.thm
    val prove_lthm : Thm.thm -> Thm.thm
    val prove_ltb : PrimitiveBddRules.term_bdd -> PrimitiveBddRules.term_bdd
    val testlz : string -> (unit -> Thm.thm) -> Thm.thm -> unit
end