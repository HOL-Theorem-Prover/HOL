signature boolSyntax =
sig
  type thm      = Thm.thm
  type term     = Term.term
  type hol_type = Type.hol_type


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
  val bool_case      : term
  val literal_case   : term
  val let_tm         : term
  val arb            : term
  val the_value      : term
  val bounded_tm     : term
  val res_forall_tm  : term
  val res_exists_tm  : term
  val res_exists1_tm : term
  val res_select_tm  : term
  val res_abstract_tm: term

  (* Construction routines *)

  val mk_eq                  : term * term -> term
  val mk_imp                 : term * term -> term
  val mk_select              : term * term -> term
  val mk_forall              : term * term -> term
  val mk_exists              : term * term -> term
  val mk_exists1             : term * term -> term
  val mk_conj                : term * term -> term
  val mk_disj                : term * term -> term
  val mk_neg                 : term -> term
  val mk_let                 : term * term -> term
  val mk_cond                : term * term * term -> term
  val mk_bool_case           : term * term * term -> term
  val mk_literal_case        : term * term -> term
  val mk_arb                 : hol_type -> term
  val mk_itself              : hol_type -> term
  val mk_res_forall          : term * term * term -> term
  val mk_res_exists          : term * term * term -> term
  val mk_res_exists_unique   : term * term * term -> term
  val mk_res_select          : term * term * term -> term
  val mk_res_abstract        : term * term * term -> term
  val mk_icomb               : term * term -> term

  (* Destruction routines *)

  val dest_eq                : term -> term * term
  val dest_eq_ty             : term -> term * term * hol_type
  val lhs                    : term -> term
  val rhs                    : term -> term
  val lhand                  : term -> term
  val rand                   : term -> term
  val rator                  : term -> term
  val dest_imp               : term -> term * term
  val dest_imp_only          : term -> term * term
  val dest_select            : term -> term * term
  val dest_forall            : term -> term * term
  val dest_exists            : term -> term * term
  val dest_exists1           : term -> term * term
  val dest_conj              : term -> term * term
  val dest_disj              : term -> term * term
  val dest_neg               : term -> term
  val dest_let               : term -> term * term
  val dest_cond              : term -> term * term * term
  val dest_bool_case         : term -> term * term * term
  val dest_literal_case      : term -> term * term
  val dest_arb               : term -> hol_type
  val dest_itself            : term -> hol_type
  val dest_res_forall        : term -> term * term * term
  val dest_res_exists        : term -> term * term * term
  val dest_res_exists_unique : term -> term * term * term
  val dest_res_select        : term -> term * term * term
  val dest_res_abstract      : term -> term * term * term


  (* Query routines *)

  val is_eq                  : term -> bool
  val is_imp                 : term -> bool
  val is_imp_only            : term -> bool
  val is_select              : term -> bool
  val is_forall              : term -> bool
  val is_exists              : term -> bool
  val is_exists1             : term -> bool
  val is_conj                : term -> bool
  val is_disj                : term -> bool
  val is_neg                 : term -> bool
  val is_cond                : term -> bool
  val is_bool_case           : term -> bool
  val is_literal_case        : term -> bool
  val is_let                 : term -> bool
  val is_arb                 : term -> bool
  val is_the_value           : term -> bool
  val is_res_forall          : term -> bool
  val is_res_exists          : term -> bool
  val is_res_exists_unique   : term -> bool
  val is_res_select          : term -> bool
  val is_res_abstract        : term -> bool

  (* Construction of a term from a list of terms *)

  val list_mk_abs            : term list * term -> term
  val list_mk_forall         : term list * term -> term
  val list_mk_exists         : term list * term -> term
  val list_mk_imp            : term list * term -> term
  val list_mk_conj           : term list -> term
  val list_mk_disj           : term list -> term
  val list_mk_fun            : hol_type list * hol_type -> hol_type
  val list_mk_res_forall     : (term * term) list * term -> term
  val list_mk_res_exists     : (term * term) list * term -> term
  val list_mk_icomb          : term * term list -> term

  val gen_all                : term -> term

  (* Destructing a term to a list of terms *)

  val strip_comb             : term -> term * term list
  val strip_abs              : term -> term list * term
  val strip_imp              : term -> term list * term
  val strip_imp_only         : term -> term list * term
  val strip_forall           : term -> term list * term
  val strip_exists           : term -> term list * term
  val strip_conj             : term -> term list
  val strip_disj             : term -> term list
  val strip_neg              : term -> term * int
  val strip_res_forall       : term -> (term * term) list * term
  val strip_res_exists       : term -> (term * term) list * term
  val strip_fun              : hol_type -> hol_type list * hol_type

  val dest_strip_comb        : term -> string * term list

  (* Connecting signature operations with grammar operations. *)

  val new_type              : string * int -> unit
  val new_infix_type        : {Name:string, Arity:int,
                               ParseName:string option, Prec:int,
                               Assoc:Parse.associativity} -> unit

  val new_constant          : string * hol_type -> unit
  val new_infix             : string * hol_type * int -> unit
  val new_binder            : string * hol_type -> unit
  val delete_const          : string -> unit
  val new_type_definition   : string * thm -> thm
  val new_infixl_definition : string * term * int -> thm
  val new_infixr_definition : string * term * int -> thm
  val new_binder_definition : string * term -> thm


  (* Lifter from ML bool to HOL bool *)

  val lift_bool : hol_type -> bool -> term

  (* Algebraic properties *)

  val comm_tm     : term
  val assoc_tm    : term
  val idem_tm     : term
  val ldistrib_tm : term
  val rdistrib_tm : term

end
