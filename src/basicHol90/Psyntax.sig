signature Psyntax =
  sig
    type term = Term.term;
    type thm = Thm.thm;
    type hol_type = Type.hol_type;
    type fixity = Term.fixity;

    val INST : (term * term) list -> thm -> thm
    val INST_TYPE : (hol_type * hol_type) list -> thm -> thm
    val INST_TY_TERM :(term*term) list * (hol_type*hol_type) list -> thm -> thm
    val SUBST : (thm * term) list -> term -> thm -> thm
    val SUBST_CONV : (thm * term) list -> term -> term -> thm
    val define_new_type_bijections : string -> string -> string ->thm -> thm
    val dest_abs : term -> (term * term)
    val dest_comb : term -> (term * term)
    val dest_cond : term -> (term * term * term)
    val dest_conj : term -> (term * term)
    val dest_cons : term -> (term * term)
    val dest_const : term -> (string * hol_type)
    val dest_disj : term -> (term * term)
    val dest_eq : term -> (term * term)
    val dest_exists : term -> (term * term)
    val dest_forall : term -> (term * term)
    val dest_imp : term -> (term * term)
    val dest_let : term -> (term * term)
    val dest_list : term -> (term list * hol_type)
    val dest_pabs : term -> (term * term)
    val dest_pair : term -> (term * term)
    val dest_select : term -> (term * term)
    val dest_type : hol_type -> (string * hol_type list)
    val dest_var : term -> (string * hol_type)
    val inst : (hol_type * hol_type) list -> term -> term
    val match_term : term -> term 
                     -> (term * term) list * (hol_type * hol_type) list
    val match_type : hol_type -> hol_type -> (hol_type * hol_type) list
    val mk_abs : (term * term) -> term
    val mk_comb : (term * term) -> term
    val mk_cond : (term * term * term) -> term
    val mk_conj : (term * term) -> term
    val mk_cons : (term * term) -> term
    val mk_const : (string * hol_type) -> term
    val mk_disj : (term * term) -> term
    val mk_eq : (term * term) -> term
    val mk_exists : (term * term) -> term
    val mk_forall : (term * term) -> term
    val mk_imp : (term * term) -> term
    val mk_let : (term * term) -> term
    val mk_list : (term list * hol_type) -> term
    val mk_pabs : (term * term) -> term
    val mk_pair : (term * term) -> term
    val mk_primed_var : (string * hol_type) -> term
    val mk_select : (term * term) -> term
    val mk_type : (string * hol_type list) -> hol_type
    val mk_var : (string * hol_type) -> term
    val new_binder : (string * hol_type) -> unit
    val new_constant : (string * hol_type) -> unit
    val new_infix : (string * hol_type * int) -> unit
    val new_recursive_definition : fixity -> thm -> string -> term -> thm
    val new_specification : string -> (string * string * int) list 
                            -> thm -> thm
    val new_type : int -> string -> unit
    val new_type_definition : (string * term * thm) -> thm
    val subst : (term * term) list -> term -> term
    val subst_occs : int list list -> (term * term) list -> term -> term
    val type_subst : (hol_type * hol_type) list -> hol_type -> hol_type
  end;
