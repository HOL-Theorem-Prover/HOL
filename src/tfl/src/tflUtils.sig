signature tflUtils =
sig
  type hol_type = Type.hol_type
  type term = Term.term

  val list_mk_type     : hol_type list -> hol_type
  val strip_type       : hol_type -> hol_type list * hol_type
  val strip_prod_type  : hol_type -> hol_type list
  val mk_vstruct       : hol_type -> term list -> term * term list

  val gen_all          : term -> term
  val strip_imp        : term -> term list * term
  val dest_relation    : term -> term * term * term
  val is_WFR           : term -> bool
  val mk_arb           : hol_type -> term
  val func_of_cond_eqn : term -> term
  val vary             : term list -> hol_type -> term

end;
