signature Opentheory = sig
type term = Term.term type hol_type = Type.hol_type type thm = Thm.thm
type thy_tyop  = OpenTheoryMap.thy_tyop
type thy_const = OpenTheoryMap.thy_const

(* record of data an article reader must provide: *)
type reader = {
  define_tyop  : string ->
                 {ax:thm, args:hol_type list, rep:string, abs:string} ->
                 {rep_abs:thm, abs_rep:thm, rep:term, abs:term, tyop:thy_tyop},
  define_const : string -> term -> {const:thy_const, def:thm},
  axiom        : thm Net.net -> (term list * term) -> thm}

(*
[tyops name info] will be called when the article wants to define a new type
with OpenTheory name [name]. [info] consists of the type axiom, a list of
arguments (type variables) for the type operator in the desired order, and the
OpenTheory names of the rep and abs constants. The call must return the new
type operator, the rep and abs constants, and the type bijection theorems.
If the type axiom is |- P t then the bijection theorems are:
  abs_rep = |- (!a. abs (rep a) = a)
  rep_abs = |- (!r. P r = (rep(abs r) = r))

[consts name rhs] will be called when the article wants to define a new
constant with OpenTheory name [name]. The call must return the (HOL) name of
the constant and an equational theorem |- const = rhs.

[axioms thms (h,c)] will be called when the article wants to retrieve an
assumption or an axiom. [thms] is the collection of theorems the article has
already proved, represented by a conclusion-indexed net. The call must return a
theorem h |- c.
*)

type 'a to_ot  = 'a OpenTheoryMap.to_ot
type 'a from_ot= 'a OpenTheoryMap.from_ot
val raw_read_article : {tyop_from_ot:thy_tyop from_ot,
                        const_from_ot:thy_const from_ot}
           -> TextIO.instream -> reader -> thm Net.net
val read_article     : string -> reader -> thm Net.net
end
