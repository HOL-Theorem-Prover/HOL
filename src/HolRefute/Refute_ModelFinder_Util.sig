signature Refute_ModelFinder_Util = sig
  datatype polarity = Pos | Neg | Neut

  exception ARG of string * string
  exception BAD of string * string
  exception TOO_SMALL of string * string
  exception TOO_LARGE of string * string
  exception NOT_SUPPORTED of string
  exception SAME of unit

  val curry3 : ('a * 'b * 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
  val pair_from_fun : (bool -> 'a) -> 'a * 'a
  val fun_from_pair : 'a * 'a -> bool -> 'a

  val int_from_bool : bool -> int
  val nat_minus : int -> int -> int
  val reasonable_power : int -> int -> int
  val exact_log : int -> int -> int
  val exact_root : int -> int -> int

  val offset_list : int list -> int list
  val index_seq : int -> int -> int list
  val filter_indices : int list -> 'a list -> 'a list
  val filter_out_indices : int list -> 'a list -> 'a list
  val fold1 : ('a -> 'a -> 'a) -> 'a list -> 'a
  val replicate_list : int -> 'a list -> 'a list
  val all_distinct_unordered_pairs_of : 'a list -> ('a * 'a) list
  val nth_combination : (int * int) list -> int -> int list
  val all_combinations : (int * int) list -> int list list
  val remove_nth : int -> 'a list -> 'a list
  val all_permutations : 'a list -> 'a list list
  val chop : int -> 'a list -> 'a list * 'a list
  val chunk_list : int -> 'a list -> 'a list list
  val chunk_list_unevenly : int list -> 'a list -> 'a list list

  val double_lookup :
    ('a * 'a -> bool) -> ('a option * 'b) list -> 'a -> 'b option
  val triple_lookup :
    (''a * ''a -> bool) -> (''a option * 'b) list -> ''a -> 'b option

  val plural_s_for_list : 'a list -> string
  val signed_string_of_int : int -> string

  val apply_within_budget : Time.time -> ('a -> 'b) -> 'a -> 'b

  val flip_polarity : polarity -> polarity

  val same_type : Type.hol_type -> Type.hol_type -> bool
  val member_type : Type.hol_type -> Type.hol_type list -> bool
  val add_type :
    Type.hol_type -> Type.hol_type list -> Type.hol_type list
  val aconv_member : Term.term -> Term.term list -> bool
  val distinct_terms : Term.term list -> Term.term list
  val update_term : Term.term -> Term.term -> Term.term -> Term.term
end
