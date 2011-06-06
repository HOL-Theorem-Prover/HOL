signature Absyn =
sig
  type term = Term.term
  type pretype = Pretype.pretype
  type 'a quotation = 'a Portable.quotation

   datatype vstruct
       = VAQ    of locn.locn * term
       | VIDENT of locn.locn * string
       | VPAIR  of locn.locn * vstruct * vstruct
       | VTYPED of locn.locn * vstruct * pretype

   datatype absyn
       = AQ     of locn.locn * term
       | IDENT  of locn.locn * string
       | QIDENT of locn.locn * string * string
       | APP    of locn.locn * absyn * absyn
       | LAM    of locn.locn * vstruct * absyn
       | TYPED  of locn.locn * absyn * pretype

  val locn_of_absyn   : absyn -> locn.locn
  val locn_of_vstruct : vstruct -> locn.locn

  val mk_AQ    : term -> absyn
  val mk_ident : string -> absyn
  val mk_app   : absyn * absyn -> absyn
  val mk_lam   : vstruct * absyn -> absyn
  val mk_typed : absyn * pretype -> absyn

  val mk_eq      : absyn * absyn -> absyn
  val mk_conj    : absyn * absyn -> absyn
  val mk_disj    : absyn * absyn -> absyn
  val mk_imp     : absyn * absyn -> absyn
  val mk_pair    : absyn * absyn -> absyn
  val mk_forall  : vstruct * absyn -> absyn
  val mk_exists  : vstruct * absyn -> absyn
  val mk_exists1 : vstruct * absyn -> absyn
  val mk_select  : vstruct * absyn -> absyn
  val mk_binder  : string -> vstruct * absyn -> absyn

  val dest_AQ      : absyn -> term
  val dest_ident   : absyn -> string
  val dest_app     : absyn -> absyn * absyn
  val dest_lam     : absyn -> vstruct * absyn
  val dest_typed   : absyn -> absyn * pretype
  val dest_eq      : absyn -> absyn * absyn
  val dest_conj    : absyn -> absyn * absyn
  val dest_disj    : absyn -> absyn * absyn
  val dest_imp     : absyn -> absyn * absyn
  val dest_pair    : absyn -> absyn * absyn
  val dest_forall  : absyn -> vstruct * absyn
  val dest_exists  : absyn -> vstruct * absyn
  val dest_exists1 : absyn -> vstruct * absyn
  val dest_select  : absyn -> vstruct * absyn
  val dest_binder  : string -> absyn -> vstruct * absyn
  val dest_binop   : string -> absyn -> absyn * absyn

  val list_mk_app     : absyn * absyn list -> absyn
  val list_mk_lam     : vstruct list * absyn -> absyn
  val list_mk_conj    : absyn list -> absyn
  val list_mk_disj    : absyn list -> absyn
  val list_mk_imp     : absyn list -> absyn
  val list_mk_pair    : absyn list -> absyn
  val list_mk_forall  : vstruct list * absyn -> absyn
  val list_mk_exists  : vstruct list * absyn -> absyn
  val list_mk_exists1 : vstruct list * absyn -> absyn
  val list_mk_select  : vstruct list * absyn -> absyn

  val strip_app     : absyn -> absyn * absyn list
  val strip_lam     : absyn -> vstruct list * absyn
  val strip_conj    : absyn -> absyn list
  val strip_disj    : absyn -> absyn list
  val strip_imp     : absyn -> absyn list
  val strip_pair    : absyn -> absyn list
  val strip_forall  : absyn -> vstruct list * absyn
  val strip_exists  : absyn -> vstruct list * absyn
  val strip_exists1 : absyn -> vstruct list * absyn
  val strip_select  : absyn -> vstruct list * absyn

  val is_ident   : absyn -> bool
  val is_app     : absyn -> bool
  val is_lam     : absyn -> bool
  val is_AQ      : absyn -> bool
  val is_typed   : absyn -> bool
  val is_eq      : absyn -> bool
  val is_conj    : absyn -> bool
  val is_disj    : absyn -> bool
  val is_imp     : absyn -> bool
  val is_pair    : absyn -> bool
  val is_forall  : absyn -> bool
  val is_exists  : absyn -> bool
  val is_exists1 : absyn -> bool
  val is_select  : absyn -> bool
end;
