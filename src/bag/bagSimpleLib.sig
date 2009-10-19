signature bagSimpleLib =
sig
  include Abbrev

  val BAG_RESORT_CONV : int list -> conv
  val BAG_IMAGE_CONV  : conv
  val GET_BAG_IN_THMS : term -> thm list

  val get_resort_position___pred       : (term -> bool) -> term -> int option
  val get_resort_list___pred           : (term -> bool) -> term -> int list
  val get_resort_positions___pred_pair : (term -> term -> bool) -> term -> term -> (int * int) option
  val get_resort_lists___pred_pair     : (term -> term -> bool) -> term -> term -> (int list * int list)
  
  val SIMPLE_BAG_NORMALISE_CONV  : conv
  val BAG_EQ_INSERT_CANCEL_CONV  : conv
  val BAG_DIFF_INSERT_CANCEL_CONV: conv
  val SUB_BAG_INSERT_CANCEL_CONV : conv
  val SUB_BAG_INSERT_SOLVE       : term -> thm

end
