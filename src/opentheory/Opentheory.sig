signature Opentheory = sig
type term = Term.term type hol_type = Type.hol_type type thm = Thm.thm
type ('a,'b) dict = ('a,'b) Redblackmap.dict

(* maps between OpenTheory names and HOL4 names: *)
type thy_tyop  = {Thy:string,Tyop:string}
type thy_const = {Thy:string,Name:string}
type 'a to_ot  = ('a,string) dict
type 'a from_ot= (string,'a) dict
val tyop_to_ot   : unit -> thy_tyop to_ot
val tyop_from_ot : unit -> thy_tyop from_ot
val const_to_ot  : unit -> thy_const to_ot
val const_from_ot: unit -> thy_const from_ot

(* record of data an article reader must provide: *)
type reader = {
  tyops  : (string, {axiom:thm, args:hol_type list, rep:string, abs:string} ->
                    {rep_abs:thm, abs_rep:thm, rep:term, abs:term, tyop:thy_tyop})
           dict,
  consts : (string, term -> {const:thy_const, def:thm}) dict,
  axioms : thm Net.net -> (term list * term) -> thm}

(*
tyops are type operators the article will define, indexed by their OpenTheory
names. Each name is mapped to a function that does something equivalent to
defining the new type. Each function is provided the type axiom, a list of
arguments (type variables) for the type operator in the desired order, and the
OpenTheory names of the rep and abs constants. It must return the new type
operator, the rep and abs constants, and the type bijection theorems.
If axiom = |- P t then these are:
  abs_rep = |- (!a. abs (rep a) = a)
  rep_abs = |- (!r. P r = (rep(abs r) = r))

consts are constants the article will define, indexed by their OpenTheory
names. Each name is mapped to a function that does something equivalent to
defining the new constant. Each function is provided the right hand side rhs of
the definition and must return the name of the constant and an equational
theorem |- const = rhs.

axioms are theorems that the article depends on about possibly both input
and output tyops and constants. They are represented by a function that takes
the collection of theorems the article has already proved, represented by a
conclusion-indexed net, and a pair (h,c) representing the desired axiom, and
must return a theorem h |- c.
*)

val raw_read_article : {tyop_from_ot:thy_tyop from_ot,
                        const_from_ot:thy_const from_ot}
           -> TextIO.instream -> reader -> thm list
val read_article     : string -> reader -> thm list
end
