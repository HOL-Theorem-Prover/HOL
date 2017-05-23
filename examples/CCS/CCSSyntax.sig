(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

signature CCSSyntax =
sig
  include Abbrev

  val args_label		: term -> term * term
  val arg_name			: term -> term
  val arg_coname		: term -> term
  val arg_action		: term -> term
  val arg_compl			: term -> term
  val arg_relabelling		: term -> term
  val arg_ccs_var		: term -> term
  val args_prefix		: term -> term * term
  val args_sum			: term -> term * term
  val args_par			: term -> term * term
  val args_restr		: term -> term * term
  val args_relab		: term -> term * term
  val args_rec			: term -> term * term

  val is_name			: term -> bool
  val is_coname			: term -> bool
  val is_label			: term -> bool
  val is_tau			: term -> bool
  val is_compl			: term -> bool
  val is_nil			: term -> bool
  val is_ccs_var		: term -> bool
  val is_prefix			: term -> bool
  val is_sum			: term -> bool
  val is_par			: term -> bool
  val is_restr			: term -> bool
  val is_relab			: term -> bool
  val is_rec			: term -> bool

  val mk_name			: term -> term
  val mk_coname			: term -> term
  val mk_label			: term -> term
  val mk_ccs_var		: term -> term
  val mk_prefix			: term * term -> term
  val mk_sum			: term * term -> term
  val mk_par			: term * term -> term
  val mk_restr			: term * term -> term
  val mk_relab			: term * term -> term
  val mk_rec			: term * term -> term

  val flat_sum			: term -> term list
  val ladd			: term -> term list -> term list
  val FIND_SMD			: term list -> term -> term list -> term -> term list * term list
  val build_sum			: term list -> term
  val sum_to_fun		: term list -> term -> term -> term

  val Label_EQ_CONV		: conv
  val Label_IN_CONV		: term -> conv
  val Action_EQ_CONV		: conv
  val Action_IN_CONV		: term -> conv
  val RELAB_EVAL_CONV		: conv

end

(* last updated: May 14, 2017 *)
