signature wfrecUtils =
sig
  include Abbrev

  val zip3              : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list
  val unzip3            : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
  val gtake             : ('a -> 'b) -> int * 'a list -> 'b list * 'a list
  val list_to_string    : ('a -> string) -> string -> 'a list -> string

  val mk_sum_type       : hol_type -> hol_type -> hol_type
  val mk_prod_type      : hol_type -> hol_type -> hol_type
  val list_mk_fun_type  : hol_type list -> hol_type
  val list_mk_prod_type : hol_type list -> hol_type
  val strip_fun_type    : hol_type -> hol_type list * hol_type
  val strip_prod_type   : hol_type -> hol_type list

  val atom_name         : term -> string
  val mk_vstruct        : hol_type -> term list -> term * term list
  val gen_all           : term -> term
  val strip_imp         : term -> term list * term
  val dest_relation     : term -> term * term * term
  val is_WFR            : term -> bool
  val func_of_cond_eqn  : term -> term
  val vary              : term list -> hol_type -> term
  val match_type        :'a -> hol_type -> hol_type -> (hol_type,hol_type)subst
  val match_term        : 'a -> term -> term 
                            -> (term,term) subst * (hol_type,hol_type) subst

end;
