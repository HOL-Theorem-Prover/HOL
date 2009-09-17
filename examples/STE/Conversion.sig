signature Conversion =
sig

  include Abbrev

  val base_defn_list : thm list

  val CONV : conv

  val STE_CONV_RULE : thm -> thm list -> thm

  val add_next : int -> term -> term
  val add_next_upto_depth : int -> int -> term -> term

  val TrajForm : term * string * term * int * int -> term
  val TF : (term * string * term * int * int) list -> term

  val extract_constr : thm -> term

  val STE : term -> term -> term -> thm list -> bool -> thm

  val STE_TO_BOOL : term -> term -> term -> term -> thm -> thm -> thm -> thm

end (* sig *)
