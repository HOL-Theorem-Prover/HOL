signature Opentheory = sig
type term = Term.term type hol_type = Type.hol_type type thm = Thm.thm
type thy_tyop  = OpenTheoryMap.thy_tyop
type thy_const = OpenTheoryMap.thy_const

(* record of data an article reader must provide: *)
type reader = {
  define_tyop  : {name:thy_tyop, ax:thm, args:hol_type list, rep:thy_const, abs:thy_const} ->
                 {rep_abs:thm, abs_rep:thm},
  define_const : thy_const -> term -> thm,
  axiom        : thm Net.net -> (term list * term) -> thm}

(*
[define_tyop r] will be called when the article wants to define a type. [r]
consists of the name of the type operator to be defined, the type axiom, a list
of arguments (type variables) for the type operator in the desired order, and
the names of the rep and abs constants. The call must return the type bijection
theorems. The type axiom will be of the form |- P t. The bijection theorems
should be:
  abs_rep = |- abs (rep a) = a
  rep_abs = |- P r = (rep(abs r) = r)

[define_const name rhs] will be called when the article wants to define a new
constant. The call must return a theorem |- const = rhs, where [const] is the
constant with name [name].

[axiom thms (h,c)] will be called when the article wants to retrieve an
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
