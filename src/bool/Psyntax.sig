signature Psyntax =
sig
  type hol_type = Type.hol_type
  type term = Term.term


  val mk_type       : string * hol_type list -> hol_type
  val mk_var        : string * hol_type -> term
  val mk_primed_var : string * hol_type -> term
  val mk_const      : string * hol_type -> term
  val mk_abs        : term * term -> term
  val mk_comb       : term * term -> term
  val mk_cond       : term * term * term -> term
  val mk_conj       : term * term -> term
  val mk_disj       : term * term -> term
  val mk_eq         : term * term -> term
  val mk_forall     : term * term -> term
  val mk_exists     : term * term -> term
  val mk_exists1    : term * term -> term
  val mk_select     : term * term -> term
  val mk_imp        : term * term -> term
  val mk_let        : term * term -> term

  val dest_type     : hol_type -> string * hol_type list
  val dest_var      : term -> string * hol_type
  val dest_const    : term -> string * hol_type
  val dest_abs      : term -> term * term
  val dest_comb     : term -> term * term
  val dest_cond     : term -> term * term * term
  val dest_conj     : term -> term * term
  val dest_disj     : term -> term * term
  val dest_eq       : term -> term * term
  val dest_forall   : term -> term * term
  val dest_exists   : term -> term * term
  val dest_exists1  : term -> term * term
  val dest_select   : term -> term * term
  val dest_imp      : term -> term * term
  val dest_imp_only : term -> term * term
  val dest_let      : term -> term * term

  val new_type      : string * int -> unit
  val new_constant  : string * hol_type -> unit
  val new_infix     : string * hol_type * int -> unit
  val new_binder    : string * hol_type -> unit

  datatype lambda 
     = VAR   of string * hol_type
     | CONST of {Name:string, Thy:string, Ty:hol_type}
     | COMB  of term * term
     | LAMB  of term * term

  val dest_term : term -> lambda
end;
