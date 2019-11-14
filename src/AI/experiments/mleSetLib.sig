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

  (* *)
  val quantl : term list
  val is_quant : term -> bool
  val norm_bvarl : term -> term
  (* operators *)
  val operl_plain : term list

  (* evaluation *)
  val eval_term : term -> int list
  val eval_subst : (term * term) -> int list -> bool
  val eval64 : term -> (bool * int) list option

  (* search *)
  val start_form : term
  val movel : term list
  val random_step : term -> term
  val apply_move_aux : term -> term -> term
  val available_move_aux : term -> term -> bool

  (* tests *)
  val imitate_once : term -> term -> term
  val imitate : term -> bool

end
