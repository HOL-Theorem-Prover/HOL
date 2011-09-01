signature liteLib =
sig
   include Abbrev

(*---------------------------------------------------------------------
 * exceptions
 *--------------------------------------------------------------------*)
(*  exception Interrupt  (* USE THIS WITH NJSML ONLY!!! *) *)

  val STRUCT_ERR  : string -> (string * string) -> 'a
  val STRUCT_WRAP : string -> (string * exn) -> 'a
  val fail        : unit -> 'a
  val failwith    : string -> 'a

(*---------------------------------------------------------------------
 * options
 *--------------------------------------------------------------------*)

  val the : 'a option -> 'a
  val is_some : 'a option -> bool
  val is_none : 'a option -> bool
  val option_cases : ('a -> 'b) -> 'b -> 'a option -> 'b
  val option_app : ('a -> 'b) -> 'a option -> 'b option

(*--------------------------------------------------------------------*
 * Some extra combinators, e.g. reverse application.                  *
 *--------------------------------------------------------------------*)

  val |> : 'a * ('a -> 'b) -> 'b
  val thenf : ('a -> 'b) * ('b -> 'c) -> 'a -> 'c
  val orelsef : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
  val repeat : ('a -> 'a) -> 'a -> 'a

(*---------------------------------------------------------------------*
 * Some extra list functions                                           *
 *---------------------------------------------------------------------*)

  (* from the basis *)
  val foldr : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
  val foldl : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b

  (* extras *)
  val rotl : 'a list -> 'a list
  val rotr : 'a list -> 'a list
  val upto : (int * int) -> int list
  val replicate : ('a * int) -> 'a list
  val chop_list : int -> 'a list -> 'a list * 'a list
  val splitlist : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  val striplist : ('a -> 'a * 'a) -> 'a -> 'a list
  val rev_splitlist : ('a -> 'a * 'b) -> 'a -> 'a * 'b list
  val end_foldr : ('a * 'a -> 'a) -> 'a list -> 'a

(*---------------------------------------------------------------------
 * Assoc lists.
 *--------------------------------------------------------------------*)

  val rev_assoc : ''b -> ('a * ''b) list -> 'a
  val add_assoc : ''a * 'b -> (''a * 'b) list -> (''a * 'b) list
  val remove_assoc : ''a -> (''a * 'b) list -> (''a * 'b) list

(*---------------------------------------------------------------------
 * Substitutions.  Nb. different to hol90.
 *--------------------------------------------------------------------*)
(*
  val |-> : ('a * 'b) -> ('b * 'a)
  val redex : ('a * 'b) -> 'b
  val residue : ('a * 'b) -> 'a
*)

(*-------------------------------------------------------------------
 * Partial Orders
 *-------------------------------------------------------------------*)

  val lt_of_ord : ('a * 'a -> order) -> ('a * 'a -> bool)
  val ord_of_lt : ('a * 'a -> bool) -> ('a * 'a -> order)
  val list_ord : ('a * 'a -> order) -> 'a list * 'a list -> order

(*---------------------------------------------------------------------
 * lazy objects
 *--------------------------------------------------------------------*)

  type ('a,'b)lazy;
  val lazy : ('a -> 'b) -> 'a -> ('a,'b) lazy;
  val eager: 'a -> ('b,'a) lazy;
  val eval : ('a,'b)lazy -> 'b;


(*--------------------------------------------------------------------*
 * Term operators                                                     *
 *--------------------------------------------------------------------*)

    val mk_binop : term -> term * term -> term
    val is_binop : term -> term -> bool
    val dest_binop : term -> term -> term * term
    val strip_binop : term -> term -> term list * term
    val binops : term -> term -> term list
    val lhand : term -> term

    val mk_icomb : term * term -> term
    val list_mk_icomb : term -> term list -> term

    (* versions which do not treat negations as implications *)
    val is_imp    : term -> bool
    val dest_imp  : term -> term * term
    val strip_imp : term -> term list * term;

    val name_of_const : term -> string * string   (* (name,segment) *)
    val alpha : term -> term -> term

    val RIGHT_BETAS : term list -> thm -> thm
    val BINDER_CONV : conv -> conv
    val BODY_CONV : conv -> conv
    val COMB2_CONV : conv -> conv -> conv
    val COMB2_QCONV : conv -> conv -> conv
    val COMB_CONV : conv -> conv
    val COMB_QCONV : conv -> conv

    val LAND_CONV : conv -> conv
    val MK_ABSL_CONV : term list -> conv
    val MK_ABS_CONV : term -> conv
    val MK_BINOP : term -> thm * thm -> thm
    val PINST : (hol_type,hol_type)subst -> (term,term)subst -> thm -> thm
    val REPEATQC : conv -> conv

    val SUB_QCONV : conv -> conv
    val SUB_CONV : conv -> conv
    val ABS_CONV : conv -> conv

    val THENCQC : conv * conv -> conv
    val THENQC : conv * conv -> conv

    val SINGLE_DEPTH_CONV : conv -> conv
    val ONCE_DEPTH_CONV : conv -> conv
    val ONCE_DEPTH_QCONV : conv -> conv
    val DEPTH_BINOP_CONV : term -> conv -> conv
    val DEPTH_CONV : conv -> conv
    val DEPTH_QCONV : conv -> conv
    val REDEPTH_CONV : conv -> conv
    val REDEPTH_QCONV : conv -> conv
    val TOP_DEPTH_CONV : conv -> conv
    val TOP_DEPTH_QCONV : conv -> conv
    val TOP_SWEEP_CONV : conv -> conv
    val TOP_SWEEP_QCONV : conv -> conv

    val MK_DISJ : thm -> thm -> thm
    val MK_CONJ : thm -> thm -> thm
    val MK_FORALL : term -> thm -> thm
    val MK_EXISTS : term -> thm -> thm

    val SIMPLE_DISJ_CASES : thm -> thm -> thm
    val SIMPLE_CHOOSE : term -> thm -> thm

end;
