signature USyntax =
sig

  type term = Term.term
  type hol_type = Type.hol_type;
  datatype ('a,'b) binding = |-> of 'a * 'b

  val alpha : hol_type
  val bool  : hol_type
  val drop_Trueprop : term -> term

  (* hol_types *)
  val type_vars  : hol_type -> hol_type list
  val type_varsl : hol_type list -> hol_type list
  val mk_type    : {Tyop: string, Args:hol_type list} -> hol_type
  val list_mk_type :hol_type list -> hol_type
  val dest_type  : hol_type -> {Tyop : string, Args : hol_type list}
  val mk_vartype : string -> hol_type
  val is_vartype : hol_type -> bool
  val -->        : hol_type * hol_type -> hol_type
  val strip_type : hol_type -> hol_type list * hol_type
  val strip_prod_type : hol_type -> hol_type list
  val match_type: hol_type -> hol_type -> (hol_type,hol_type) binding list

  (* terms *)
  val free_vars  : term -> term list
  val free_varsl : term list -> term list
  val free_vars_lr : term -> term list
  val all_vars   : term -> term list
  val all_varsl  : term list -> term list
  val variant    : term list -> term -> term
  val type_of    : term -> hol_type
  val type_vars_in_term : term -> hol_type list
  val dest_term  : term -> Term.term Term.lambda
  
  (* Prelogic *)
  val aconv     : term -> term -> bool
  val subst     : (term,term) binding list -> term -> term
  val inst      : (hol_type,hol_type) binding list -> term -> term
  val beta_conv : term -> term

  (* Construction routines *)
  val mk_prop   :term -> term
  val mk_var    :{Name : string, Ty : hol_type} -> term
  val mk_const  :{Name : string, Ty : hol_type} -> term
  val mk_comb   :{Rator : term, Rand : term} -> term
  val mk_abs    :{Bvar  : term, Body : term} -> term

  val mk_eq     :{lhs : term, rhs : term} -> term
  val mk_imp    :{ant : term, conseq :  term} -> term
  val mk_select :{Bvar : term, Body : term} -> term
  val mk_forall :{Bvar : term, Body : term} -> term
  val mk_exists :{Bvar : term, Body : term} -> term
  val mk_conj   :{conj1 : term, conj2 : term} -> term
  val mk_disj   :{disj1 : term, disj2 : term} -> term
  val mk_pabs   :{varstruct : term, body : term} -> term

  (* Destruction routines *)
  val dest_var  : term -> {Name : string, Ty : hol_type}
  val dest_const: term -> {Name : string, Ty : hol_type}
  val dest_comb : term -> {Rator : term, Rand : term}
  val dest_abs  : term -> {Bvar : term, Body : term}
  val dest_eq     : term -> {lhs : term, rhs : term}
  val dest_imp    : term -> {ant : term, conseq : term}
  val dest_select : term -> {Bvar : term, Body : term}
  val dest_forall : term -> {Bvar : term, Body : term}
  val dest_exists : term -> {Bvar : term, Body : term}
  val dest_neg    : term -> term
  val dest_conj   : term -> {conj1 : term, conj2 : term}
  val dest_disj   : term -> {disj1 : term, disj2 : term}
  val dest_pair   : term -> {fst : term, snd : term}
  val dest_pabs   : term -> {varstruct : term, body : term}

  val lhs   : term -> term
  val rhs   : term -> term
  val rator : term -> term
  val rand  : term -> term
  val bvar  : term -> term
  val body  : term -> term
  

  (* Query routines *)
  val is_var  : term -> bool
  val is_const: term -> bool
  val is_comb : term -> bool
  val is_abs  : term -> bool
  val is_eq     : term -> bool
  val is_imp    : term -> bool
  val is_forall : term -> bool 
  val is_exists : term -> bool 
  val is_neg    : term -> bool
  val is_conj   : term -> bool
  val is_disj   : term -> bool
  val is_pair   : term -> bool
  val is_pabs   : term -> bool

  (* Construction of a term from a list of terms *)
  val list_mk_comb   : (term * term list) -> term
  val list_mk_abs    : (term list * term) -> term
  val list_mk_imp    : (term list * term) -> term
  val list_mk_forall : (term list * term) -> term
  val list_mk_exists : (term list * term) -> term
  val list_mk_conj   : term list -> term
  val list_mk_disj   : term list -> term

  (* Destructing a term to a list of terms *)
  val strip_comb     : term -> (term * term list)
  val strip_abs      : term -> (term list * term)
  val strip_imp      : term -> (term list * term)
  val strip_forall   : term -> (term list * term)
  val strip_exists   : term -> (term list * term)
  val strip_conj     : term -> term list
  val strip_disj     : term -> term list
  val strip_pair     : term -> term list

  (* Miscellaneous *)
  val mk_vstruct : hol_type -> term list -> term * term list
  val gen_all    : term -> term
  val find_term  : (term -> bool) -> term -> term
  val find_terms : (term -> bool) -> term -> term list
  val dest_relation : term -> term * term * term
  val is_WFR : term -> bool
  val ARB : hol_type -> term

  (* Prettyprinting *)
  val term_to_string : term -> string
end;
