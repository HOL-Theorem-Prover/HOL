(* ===================================================================== *)
(* FILE          : lib.sig                                               *)
(* DESCRIPTION   : Signature for library of useful SML functions.        *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


(*---------------------------------------------------------------------
 * In general, the Lib structure is an extension of the Portable structure to
 * to include lots of useful things whose implementations are pretty
 * uncontroversial.
 *
 * Typically, whenever a group of functions is extended, the Lib structure will
 * also include the Portable functions for that datatype.
 *--------------------------------------------------------------------*)


signature LiteLib =
sig


(*---------------------------------------------------------------------
 * exceptions
 *--------------------------------------------------------------------*)
(*  exception Interrupt  (* USE THIS WITH NJSML ONLY!!! *) *)
  val STRUCT_ERR : string -> (string * string) -> 'a
  val STRUCT_WRAP : string -> (string * exn) -> 'a
  val fail : unit -> 'b
  val failwith : string -> 'a

(*---------------------------------------------------------------------
 * options
 *--------------------------------------------------------------------*)

  val the : 'a option -> 'a
  val is_some : 'a option -> bool
  val is_none : 'a option -> bool
  val option_cases : ('a -> 'b) -> 'b -> 'a option -> 'b
  val option_app : ('a -> 'b) -> 'a option -> 'b option

(*---------------------------------------------------------------------
 * Curry/Uncurry/Combinators/Reverse Application
 *--------------------------------------------------------------------*)

  val |> : 'a * ('a -> 'b) -> 'b
  val thenf : ('a -> 'b) * ('b -> 'c) -> 'a -> 'c
  val orelsef : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
  val W : ('a -> 'a -> 'b) -> 'a -> 'b
  val repeat : ('a -> 'a) -> 'a -> 'a


(*---------------------------------------------------------------------
 * Curried versions of some functions
 *--------------------------------------------------------------------*)

  val append : 'a list -> 'a list -> 'a list

(*---------------------------------------------------------------------
 * A (semi-)complete set of list functions
 *
 *--------------------------------------------------------------------*)

  (* from the basis *)
  val hd : 'a list -> 'a  (* raises HOL_ERR *)
  val tl : 'a list -> 'a list (* raises HOL_ERR *)
  val filter : ('a -> bool) -> 'a list -> 'a list
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
  val qpartition : (''a -> bool) -> ''a list -> (''a list -> ''a list * ''a list)

  val foldr : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
  val foldl : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
  val all : ('a -> bool) -> 'a list -> bool

  (* extras *)
  val tryfind : ('a -> 'b) -> 'a list -> 'b
  val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val first : ('a -> bool) -> 'a list -> 'a
  val split_after : int -> 'a list -> 'a list * 'a list
  val chop_list : int -> 'a list -> 'a list * 'a list (* synonyms *)
  val combine : 'a list * 'b list -> ('a * 'b) list
  val split : ('a * 'b) list -> 'a list * 'b list
  val mapfilter : ('a -> 'b) -> 'a list -> 'b list
  val flatten : 'a list list -> 'a list
  val rotl : 'a list -> 'a list
  val rotr : 'a list -> 'a list
  val front_n_back : 'a list -> ('a list * 'a)
  val sort : ('a -> 'a -> bool) -> 'a list -> 'a list
  val int_sort : int list -> int list
  val replicate : ('a * int) -> 'a list
  val upto : (int * int) -> int list
  val splitlist : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  val striplist : ('a -> 'a * 'a) -> 'a -> 'a list
  val rev_splitlist : ('a -> 'a * 'b) -> 'a -> 'a * 'b list
  val end_foldr : ('a * 'a -> 'a) -> 'a list -> 'a

  val gather : ('a -> bool) -> 'a list -> 'a list
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val unzip : ('a * 'b) list -> 'a list * 'b list
  val el : int -> 'a list -> 'a
  val itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val itlist2 :('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val rev_itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev_itlist2 :('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a

(*---------------------------------------------------------------------
 * Assoc lists.  Nb. diff. to hol90.  raise Subscript on failure.
 *--------------------------------------------------------------------*)

  exception Subscript
  val assoc : ''a -> (''a * 'b) list -> 'b
  val rev_assoc : ''b -> ('a * ''b) list -> 'a
  val add_assoc : ''a * 'b -> (''a * 'b) list -> (''a * 'b) list
  val remove_assoc : ''a -> (''a * 'b) list -> (''a * 'b) list
  val |--> : ('a * 'b) -> ('a * 'b)

(*---------------------------------------------------------------------
 * Substitutions.  Nb. different to hol90.
 *--------------------------------------------------------------------*)

  val |-> : ('a * 'b) -> ('b * 'a)
  val redex : ('a * 'b) -> 'b
  val residue : ('a * 'b) -> 'a

(*---------------------------------------------------------------------
 * Sets where equality is "=" (repr. by lists)
 *--------------------------------------------------------------------*)

  val insert : ''a -> ''a list -> ''a list

(*---------------------------------------------------------------------
 * Lists/Sets where equality is supplied
 *--------------------------------------------------------------------*)

  val op_insert : ('a * 'a -> bool) -> 'a -> 'a list -> 'a list
  val op_mem : ('a * 'b -> bool) -> 'a -> 'b list -> bool
  val op_union : ('a * 'a -> bool) -> 'a list -> 'a list -> 'a list

  val remove : ('a -> bool) -> 'a list -> 'a * 'a list

(*---------------------------------------------------------------------
 * Strings
 *--------------------------------------------------------------------*)

  val string_variant : string list -> string -> string
  val hash_string : string -> int

(*-------------------------------------------------------------------
 * Partial Orders
 *-------------------------------------------------------------------*)

  datatype ordering = GREATER | LESS | EQUAL;
  val lt_of_ord : ('a * 'a -> ordering) -> ('a * 'a -> bool)
  val ord_of_lt : ('a * 'a -> bool) -> ('a * 'a -> ordering)
  val list_ord : ('a * 'a -> ordering) -> ('a list * 'a list) -> ordering

(*---------------------------------------------------------------------
 * delta's implemented by UNCHANGED exception
 *--------------------------------------------------------------------*)

  exception UNCHANGED
  val fun_to_qfun : (''a -> ''a) -> (''a -> ''a)
  val qfun_to_fun : ('a -> 'a) -> ('a -> 'a)
  val app2_qfun : (('a -> 'a) * ('b -> 'b)) -> ('a * 'b) -> ('a * 'b)
  val qmap : ('a -> 'a) -> 'a list -> 'a list

(*---------------------------------------------------------------------
 * lazy objects
 *--------------------------------------------------------------------*)

type ('a,'b)lazy;
val lazy : ('_a-> '_b) -> '_a -> ('_a,'_b) lazy;
val eager: '_a -> ('_b,'_a) lazy;
val eval : ('a,'b)lazy -> 'b;

end (* sig *)

