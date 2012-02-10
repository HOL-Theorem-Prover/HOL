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

val axiom_in_db : thm Net.net -> (term list * term) -> thm
(*
An axiom function for readers that tries to find the desired theorem in the
following places (in order): an internal list of theorems that should be in
the OpenTheory base package, the HOL4 database (via DB.match []), and the
theorems already proved by the article.
*)

val define_tyop_in_thy :
  {name:thy_tyop, ax:thm, args:hol_type list, rep:thy_const, abs:thy_const}
    -> {rep_abs:thm, abs_rep:thm}
val define_const_in_thy : (string -> string) -> thy_const -> term -> thm
(*
define_tyop and define_const functions for readers that try to produce the
desired theorems by actually defining a new type or constant in the current
theory. They fail if the theory of the type or constant desired is not the
current theory. The first argument to [define_const_in_thy] is a function to
produce the prefix of the ML name of the constant's definition from the
constant's name (useful when a constant's name is not a valid ML identifier).
*)

val raw_read_article : TextIO.instream -> reader -> thm Net.net
val read_article     : string -> reader -> thm Net.net

val delete_unused_consts : thm list -> unit
(*
Given a list (usually by calling [Net.listItems] on the result of
[read_article]), calls [Theory.delete_const] on any constants in the current
theory that do not appear in some theorem in the list.
*)

val NUMERAL_conv : Conv.conv

end
