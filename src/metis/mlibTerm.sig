(* ========================================================================= *)
(* BASIC FIRST-ORDER LOGIC MANIPULATIONS                                     *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibTerm =
sig

type 'a pp = 'a mlibUseful.pp
type ('a,'b) maplet = ('a, 'b) mlibUseful.maplet
type 'a quotation = 'a mlibParser.quotation
type infixities = mlibParser.infixities

(* Datatypes for terms and formulas *)
datatype term =
  Var of string
| Fn  of string * term list

datatype formula =
  True
| False
| Atom   of term
| Not    of formula
| And    of formula * formula
| Or     of formula * formula
| Imp    of formula * formula
| Iff    of formula * formula
| Forall of string * formula
| Exists of string * formula

(* Contructors and destructors *)
val dest_var : term -> string
val is_var   : term -> bool

val dest_fn     : term -> string * term list
val is_fn       : term -> bool
val fn_name     : term -> string
val fn_args     : term -> term list
val fn_arity    : term -> int
val fn_function : term -> string * int

val mk_const   : string -> term
val dest_const : term -> string
val is_const   : term -> bool

val mk_binop   : string -> term * term -> term
val dest_binop : string -> term -> term * term
val is_binop   : string -> term -> bool

val dest_atom : formula -> term
val is_atom   : formula -> bool

val dest_neg : formula -> formula
val is_neg   : formula -> bool

val list_mk_conj : formula list -> formula
val strip_conj   : formula -> formula list
val flatten_conj : formula -> formula list

val list_mk_disj : formula list -> formula
val strip_disj   : formula -> formula list
val flatten_disj : formula -> formula list

val list_mk_forall : string list * formula -> formula
val strip_forall   : formula -> string list * formula

val list_mk_exists : string list * formula -> formula
val strip_exists   : formula -> string list * formula

(* New variables *)
val new_var  : unit -> term
val new_vars : int -> term list

(* Sizes of terms and formulas *)
val term_size    : term -> int
val formula_size : formula -> int

(* Total comparison functions for terms and formulas *)
val term_compare    : term * term -> order
val formula_compare : formula * formula -> order

(* Operations on literals *)
val mk_literal   : bool * formula -> formula
val dest_literal : formula -> bool * formula
val is_literal   : formula -> bool
val literal_atom : formula -> formula

(* Operations on formula negations *)
val negative : formula -> bool
val positive : formula -> bool
val negate   : formula -> formula

(* Functions and relations in a formula *)
val functions      : formula -> (string * int) list
val function_names : formula -> string list
val relations      : formula -> (string * int) list
val relation_names : formula -> string list

(* The equality relation has a special status *)
val eq_rel    : string * int
val mk_eq     : term * term -> formula
val dest_eq   : formula -> term * term
val is_eq     : formula -> bool
val refl      : term -> formula
val sym       : formula -> formula
val lhs       : formula -> term
val rhs       : formula -> term
val eq_occurs : formula -> bool

(* Free variables *)
val FVT        : term -> string list
val FVTL       : string list -> term list -> string list
val FV         : formula -> string list
val FVL        : string list -> formula list -> string list
val specialize : formula -> formula
val generalize : formula -> formula

(* Subterms *)
val subterm          : int list -> term -> term
val rewrite          : (int list, term) maplet -> term -> term
val subterms         : int list -> term -> (int list, term) maplet list
val literal_subterm  : int list -> formula -> term
val literal_rewrite  : (int list, term) maplet -> formula -> formula
val literal_subterms : formula -> (int list, term) maplet list

(* A datatype to antiquote both terms and formulas *)
datatype thing = mlibTerm of term | Formula of formula;

(* Operators parsed and printed infix *)
val infixes : infixities ref

(* Deciding whether a string denotes a variable or constant *)
val var_string : (string -> bool) ref

(* Parsing *)
val string_to_term'    : infixities -> string -> term  (* purely functional *)
val string_to_formula' : infixities -> string -> formula
val parse_term'        : infixities -> thing quotation -> term
val parse_formula'     : infixities -> thing quotation -> formula
val string_to_term     : string -> term                (* uses !infixes *)
val string_to_formula  : string -> formula
val parse_term         : thing quotation -> term
val parse_formula      : thing quotation -> formula

(* Pretty-printing *)
val pp_term'           : infixities -> term pp         (* purely functional *)
val pp_formula'        : infixities -> formula pp
val term_to_string'    : infixities -> int -> term -> string
val formula_to_string' : infixities -> int -> formula -> string
val pp_term            : term pp                       (* uses !infixes    *)
val pp_formula         : formula pp                    (* and !LINE_LENGTH *)
val term_to_string     : term -> string
val formula_to_string  : formula -> string

end
