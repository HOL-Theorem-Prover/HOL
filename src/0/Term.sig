signature Term =
sig
  type hol_type = KernelTypes.hol_type
  type term = KernelTypes.term
  type ('a,'b)subst = ('a,'b)Lib.subst
  type 'a set       = 'a HOLset.set

  val termsig       : KernelTypes.holty KernelSig.symboltable

  val type_of       : term -> hol_type
  val free_vars     : term -> term list
  val free_vars_lr  : term -> term list
  val FVL           : term list -> term set -> term set
  val free_in       : term -> term -> bool
  val all_vars      : term -> term list
  val free_varsl    : term list -> term list
  val all_varsl     : term list -> term list
  val type_vars_in_term : term -> hol_type list
  val var_occurs    : term -> term -> bool
  val tyvar_occurs  : hol_type -> term -> bool
  val genvar        : hol_type -> term
  val genvars       : hol_type -> int -> term list
  val variant       : term list -> term -> term
  val prim_variant  : term list -> term -> term
  val mk_var        : string * hol_type -> term
  val mk_primed_var : string * hol_type -> term
  val dest_var      : term -> string * hol_type

  val decls         : string -> term list
  val all_consts    : unit -> term list
  val mk_const      : string * hol_type -> term
  val prim_mk_const : {Thy:string,Name:string} -> term
  val mk_thy_const  : {Thy:string, Name:string, Ty:hol_type} -> term
  val dest_const    : term -> string * hol_type
  val dest_thy_const: term -> {Thy:string, Name:string, Ty:hol_type}

  val mk_comb       : term * term -> term
  val list_mk_comb  : term * term list -> term
  val dest_comb     : term -> term * term

  val mk_tycomb     : term * hol_type -> term
  val list_mk_tycomb: term * hol_type list -> term
  val dest_tycomb   : term -> term * hol_type

  val mk_abs        : term * term -> term
  val list_mk_abs   : term list * term -> term
  val list_mk_binder: term option -> term list * term -> term
  val dest_abs      : term -> term * term
  val strip_abs     : term -> term list * term
  val strip_binder  : term option -> term -> term list * term

  val mk_tyabs      : hol_type * term -> term
  val list_mk_tybinder : term option -> hol_type list * term -> term
  val list_mk_tyabs : hol_type list * term -> term
  val dest_tyabs    : term -> hol_type * term
  val strip_tybinder: term option -> term -> hol_type list * term
  val strip_tyabs   : term -> hol_type list * term

  val is_var        : term -> bool
  val is_bvar       : term -> bool
  val is_genvar     : term -> bool
  val is_const      : term -> bool
  val is_comb       : term -> bool
  val is_tycomb     : term -> bool
  val is_abs        : term -> bool
  val is_tyabs      : term -> bool
  val rator         : term -> term
  val rand          : term -> term
  val bvar          : term -> term
  val body          : term -> term
  val rename_bvar   : string -> term -> term
  val rename_btyvar : string -> term -> term

  val same_const    : term -> term -> bool
  val aconv         : term -> term -> bool
  val beta_conv     : term -> term
  val eta_conv      : term -> term
  val ty_beta_conv  : term -> term
  val ty_eta_conv   : term -> term
  val subst         : (term,term) Lib.subst -> term -> term
  val inst          : (hol_type,hol_type) subst -> term -> term

  val raw_match     : hol_type list -> term set
                      -> term -> term
                      -> (term,term)subst * (hol_type,hol_type)subst
                      -> ((term,term)subst * term set) *
                         ((hol_type,hol_type)subst * hol_type list)
  val match_terml   : hol_type list -> term set -> term -> term
                        -> (term,term)subst * (hol_type,hol_type)subst
  val match_term    : term -> term -> (term,term)subst*(hol_type,hol_type)subst
  val norm_subst    : ((term,term)subst * term set) *
                      ((hol_type,hol_type)subst * hol_type list)
                      -> ((term,term)subst * (hol_type,hol_type)subst)
  val thy_consts    : string -> term list
  val compare       : term * term -> order
  val term_eq       : term -> term -> bool
  val var_compare   : term * term -> order
  val empty_tmset   : term set
  val empty_varset  : term set

  val lazy_beta_conv : term -> term
  val imp            : term
  val dest_eq_ty     : term -> term * term * hol_type
  val prim_mk_eq     : hol_type -> term -> term -> term
  val prim_mk_imp    : term -> term -> term
  val break_const    : term -> KernelTypes.id * hol_type
  val break_abs      : term -> term
  val break_tyabs    : term -> term
  val trav           : (hol_type -> unit) -> (term -> unit) -> term -> unit
  val ty2tm          : hol_type -> term
  val pp_raw_term    : (term -> int) -> Portable.ppstream -> term -> unit
end;
