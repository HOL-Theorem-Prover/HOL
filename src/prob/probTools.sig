signature probTools =
sig
  include Abbrev

  val grab : 'a option -> 'a
  val total : ('a -> 'b) -> 'a -> 'b option
  val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val ## : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
  val I : 'a -> 'a
  val D : 'a -> 'a * 'a
  val Df : ('a -> 'b) -> 'a * 'a -> 'b * 'b
  val K : 'a -> 'b -> 'a
  val N : int -> ('a -> 'a) -> 'a -> 'a
  val index : ''a -> ''a list -> int option
  val map_partial : ('a -> 'b option) -> 'a list -> 'b list
  val cart : 'a list -> 'b list -> ('a * 'b) list
  val cart_map_partial : ('a * 'b -> 'c option) -> 'a list * 'b list -> 'c list
  val assoc : ''a -> (''a * 'b) list -> 'b option

  val new_int : unit -> int

  val sort : ('a * 'a -> bool) -> 'a list -> 'a list
  val top_sort : (''a * ''a -> bool) -> ''a list -> ''a list

  val permute : int list -> 'a list -> 'a list
  val permute_random : 'a list -> 'a list

  type sequent = term list * term

  val is_imp : term -> bool
  val profile : ('a -> 'b) -> 'a -> 'b

  val type_fold : (string * 'a -> 'b)
    -> ((string * ('a -> 'b) list) * 'a -> 'b)
    -> hol_type -> 'a -> 'b

  val term_fold : ((string * hol_type) * 'a -> 'b)
    -> ((string * hol_type) * 'a -> 'b)
    -> ((('a -> 'b) * ('a -> 'b)) * 'a -> 'b)
    -> ((('a -> 'b) * ('a -> 'b)) * 'a -> 'b)
    -> Term.term -> 'a -> 'b

  val parse_with_goal : term frag list -> sequent -> term

  val DEPTH_ONCE_CONV : conv -> conv

  val THEN1 : tactic * tactic -> tactic
  val REVERSE : tactic -> tactic

  val UNDISCH_ALL_TAC : tactic
  val KILL_ALL_TAC : tactic
  val SUFF_TAC : term frag list -> tactic
  val KNOW_TAC : term frag list -> tactic

end
