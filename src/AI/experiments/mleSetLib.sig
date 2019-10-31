signature mleSetLib =
sig

  include Abbrev

  (* reading formulas *)
  val parse_setsyntdata : unit -> (term * int list) list

  val nat_to_bin : int -> int list
  val bin_to_nat : int list -> int

  (* variables *)
  val xvar : term
  val xvarl : term list
  val yvarl : term list
  val is_xyvar : term -> bool
  
  (* continuations *)
  val cont_form : term
  val cont_term : term
  val is_cont : term -> bool

  (* operators *)
  val operl_plain : term list

  (* evaluation *)
  val eval_term : term -> int list
  val eval_subst : (term * term) -> int list -> bool
  
  (* search *)
  val start_form : term
  val movel : term list
  val random_step : term -> term
  val apply_move : term -> term -> term
  val is_applicable : term -> term -> bool

end
