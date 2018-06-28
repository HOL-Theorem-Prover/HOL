signature hhTranslate =
sig

include Abbrev

  val log_flag : bool ref
  val log : string -> unit
  val log_t : string -> ('a -> 'b) -> 'a -> 'b
  val log_st : real -> string -> ('a -> 'b) -> 'a -> 'b
  
  val rename_bvarl : term -> term
  val all_bvar  : term -> term list  
  val must_pred : term -> bool
  val no_lambda : term -> bool
  val no_pred   : term -> bool
  val collect_arity : term -> (term, int list) Redblackmap.dict
  val has_fofarity_bv : term -> bool

  val ATOM_CONV     : conv -> conv
  val LIFT_CONV     : conv
  val RPT_LIFT_CONV : term -> thm list
  val LET_CONV_BVL  : conv

  val strip_type  : hol_type -> (hol_type list * hol_type)
  val mk_arity_eq : term -> int -> thm
  val optim_arity_eq : term -> thm list
  val all_arity_eq : term -> thm list
  
  val translate_tm       : term -> term list
  val translate_pb       : (string * thm) list -> term -> 
    term list * (string * term list) list * term list
  val name_pb : 
    term list * (string * term list) list * term list ->
    (string * term) list * term

end
