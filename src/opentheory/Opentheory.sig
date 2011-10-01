signature Opentheory = sig
type term = Term.term type hol_type = Type.hol_type type thm = Thm.thm
type thy_tyop  = OpenTheoryMap.thy_tyop
type thy_const = OpenTheoryMap.thy_const
type otname    = OpenTheoryMap.otname

(* record of data an article reader must provide: *)
type reader = {
  define_tyop  : {name:thy_tyop, ax:thm, args:hol_type list, rep:thy_const, abs:thy_const} ->
                 {rep_abs:thm, abs_rep:thm},
  define_const : thy_const -> term -> thm,
  axiom        : thm Net.net -> (term list * term) -> thm,
  const_name   : otname -> thy_const,
  tyop_name    : otname -> thy_tyop}

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

[const_name n] and [tyop_name n] will be called to translate OpenTheory names
to HOL4 names. The following functions can be used to simply look the names up in the global OpenTheory map.
*)
val const_name_in_map : otname -> thy_const
val tyop_name_in_map  : otname -> thy_tyop

val raw_read_article : TextIO.instream -> reader -> thm Net.net
val read_article     : string -> reader -> thm Net.net
end
