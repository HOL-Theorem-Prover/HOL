signature hhTranslate =
sig

include Abbrev

  val is_tptp_fv : term -> bool
  val is_tptp_bv : term -> bool
  val is_app : term -> bool
  val atoms : term -> term list
  val must_pred : term -> bool
  
  (* conversions *)
  val ATOM_CONV     : conv -> conv
  val LIFT_CONV     : (int * int) ref -> conv
  val RPT_LIFT_CONV : (int * int) ref -> term -> thm list
  val APP_CONV_MIN  : conv
  val APP_CONV_AUX  : conv
  val APP_CONV_BVL  : conv
  val APP_CONV_TFF  : conv
  val APP_CONV_TFF_REC : conv  

  (* arity equations *)
  val strip_type : hol_type -> (hol_type list * hol_type)
  val collect_arity : term -> (term * int) list
  val mk_arity_eq : (term * int) -> term
  val all_arity_eq : term -> term list

  (* translation: uses a cache *)
  val translate : term -> (term * term list)
  val translate_thm : thm -> (term * term list)


end
