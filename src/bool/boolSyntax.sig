(* ===================================================================== *)
(* FILE          : boolSyntax.sig                                        *)
(* DESCRIPTION   : Derived syntax operations for elements in boolTheory  *)
(*                 (and earlier). Mostly translated from the original    *)
(*                 hol88 source.                                         *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon, University of Cambridge              *)
(*                     Konrad Slind, University of Calgary               *)
(* Modified      : September 1997, Ken Larsen (functor removal)          *)
(* Modified      : July 2000, Konrad Slind                               *)
(* ===================================================================== *)


signature boolSyntax =
sig
  type thm          = Thm.thm
  type term         = Term.term
  type hol_type     = Type.hol_type


  (* Constants *)

  val equality       : term
  val implication    : term
  val select         : term
  val T              : term
  val F              : term
  val universal      : term
  val existential    : term
  val exists1        : term
  val conjunction    : term
  val disjunction    : term
  val negation       : term
  val conditional    : term
  val letc           : term
  val arb            : term

  (* Construction routines *)

  val mk_eq          : {lhs:term, rhs:term} -> term
  val mk_imp         : {ant:term, conseq:term} -> term
  val mk_select      : {Bvar:term, Body:term} -> term
  val mk_forall      : {Bvar:term, Body:term} -> term
  val mk_exists      : {Bvar:term, Body:term} -> term
  val mk_exists1     : {Bvar:term, Body:term} -> term
  val mk_conj        : {conj1:term, conj2:term} -> term
  val mk_disj        : {disj1:term, disj2:term} -> term
  val mk_neg         : term -> term
  val mk_cond        : {cond:term, larm:term, rarm:term} -> term
  val mk_let         : {func:term, arg:term} -> term
  val mk_arb         : hol_type -> term

  (* Destruction routines *)

  val dest_eq        : term -> {lhs:term, rhs:term}
  val dest_eq_ty     : term -> {lhs:term, rhs:term, ty:hol_type}
  val lhs            : term -> term
  val rhs            : term -> term
  val dest_imp       : term -> {ant:term, conseq:term}
  val dest_imp_only  : term -> {ant:term, conseq:term}
  val dest_select    : term -> {Bvar:term, Body:term}
  val dest_forall    : term -> {Bvar:term, Body:term}
  val dest_exists    : term -> {Bvar:term, Body:term}
  val dest_exists1   : term -> {Bvar:term, Body:term}
  val dest_conj      : term -> {conj1:term, conj2:term}
  val dest_disj      : term -> {disj1:term, disj2:term}
  val dest_neg       : term -> term
  val dest_cond      : term -> {cond:term, larm:term, rarm:term}
  val dest_let       : term -> {func:term, arg:term}
  val dest_arb       : term -> hol_type

  (* Query routines *)

  val is_eq          : term -> bool
  val is_imp         : term -> bool
  val is_imp_only    : term -> bool
  val is_select      : term -> bool
  val is_forall      : term -> bool
  val is_exists      : term -> bool
  val is_exists1     : term -> bool
  val is_conj        : term -> bool
  val is_disj        : term -> bool
  val is_neg         : term -> bool
  val is_cond        : term -> bool
  val is_let         : term -> bool
  val is_arb         : term -> bool

  (* Construction of a term from a list of terms *)

  val list_mk_abs    : term list * term -> term
  val list_mk_forall : term list * term -> term
  val list_mk_exists : term list * term -> term
  val list_mk_imp    : term list * term -> term
  val list_mk_conj   : term list -> term
  val list_mk_disj   : term list -> term
  val list_mk_fun    : hol_type list * hol_type -> hol_type
  val gen_all        : term -> term

  (* Destructing a term to a list of terms *)

  val strip_comb     : term -> term * term list
  val strip_abs      : term -> term list * term
  val strip_imp      : term -> term list * term
  val strip_forall   : term -> term list * term
  val strip_exists   : term -> term list * term
  val strip_conj     : term -> term list
  val strip_disj     : term -> term list
  val strip_fun      : hol_type -> hol_type list * hol_type


  (* Connecting signature operations with grammar operations. *)

  val new_type              : {Name:string, Arity:int} -> unit
  val new_infix_type        : {Name:string, Arity:int, 
                               ParseName:string option, Prec:int,
                               Assoc:Parse.associativity} -> unit

  val new_constant          : {Name:string, Ty:hol_type} -> unit
  val new_infix             : {Name:string, Ty:hol_type, Prec:int} -> unit
  val new_binder            : {Name:string, Ty:hol_type} -> unit
  val new_type_definition   : string * thm -> thm
  val new_infixl_definition : string * term * int -> thm
  val new_infixr_definition : string * term * int -> thm
  val new_binder_definition : string * term -> thm
  val new_specification     : {name:string, sat_thm:thm,
                               consts:{fixity:Parse.fixity, 
                                       const_name:string} list} -> thm
end
