signature Rsyntax =
sig
  type hol_type = Type.hol_type
  type term = Term.term
  type thm = Thm.thm

  val mk_type       : {Args:hol_type list, Tyop:string} -> hol_type
  val mk_var        : {Name:string, Ty:hol_type} -> term 
  val mk_primed_var : {Name:string, Ty:hol_type} -> term
  val mk_const      : {Name:string, Ty:hol_type} -> term
  val mk_abs        : {Bvar:term, Body:term} -> term
  val mk_comb       : {Rand:term, Rator:term} -> term
  val mk_cond       : {cond:term, larm:term, rarm:term} -> term
  val mk_conj       : {conj1:term, conj2:term} -> term
  val mk_disj       : {disj1:term, disj2:term} -> term
  val mk_eq         : {lhs:term, rhs:term} -> term
  val mk_forall     : {Bvar:term, Body:term} -> term
  val mk_exists     : {Bvar:term, Body:term} -> term
  val mk_exists1    : {Bvar:term, Body:term} -> term
  val mk_select     : {Bvar:term, Body:term} -> term
  val mk_imp        : {ant:term, conseq:term} -> term
  val mk_let        : {arg:term, func:term} -> term

  val dest_type     : hol_type -> {Args:hol_type list, Tyop:string}
  val dest_var      : term -> {Name:string, Ty:hol_type}
  val dest_const    : term -> {Name:string, Ty:hol_type}
  val dest_abs      : term -> {Body:term, Bvar:term}
  val dest_comb     : term -> {Rand:term, Rator:term}
  val dest_cond     : term -> {cond:term, larm:term, rarm:term}
  val dest_conj     : term -> {conj1:term, conj2:term}
  val dest_disj     : term -> {disj1:term, disj2:term}
  val dest_eq       : term -> {lhs:term, rhs:term}
  val dest_forall   : term -> {Bvar:term, Body:term}
  val dest_exists   : term -> {Bvar:term, Body:term}
  val dest_exists1  : term -> {Bvar:term, Body:term}
  val dest_select   : term -> {Bvar:term, Body:term}
  val dest_imp      : term -> {ant:term, conseq:term}
  val dest_imp_only : term -> {ant:term, conseq:term}
  val dest_let      : term -> {arg:term, func:term}

  val new_type      : {Arity:int, Name:string} -> unit
  val new_constant  : {Name:string, Ty:hol_type} -> unit
  val new_infix     : {Name:string, Prec:int, Ty:hol_type} -> unit
  val new_binder    : {Name:string, Ty:hol_type} -> unit
  val new_specification : {name    : string, 
                           sat_thm : thm,
                           consts  : {const_name : string,
                                      fixity : Parse.fixity} list} -> thm
  datatype lambda 
     = VAR   of {Name:string, Ty:hol_type}
     | CONST of {Name:string, Thy:string, Ty:hol_type}
     | COMB  of {Rator:term, Rand:term}
     | LAMB  of {Bvar:term, Body:term};

  val dest_term : term -> lambda
end
