signature Refute_ModelFinder_Names = sig
  type term = Term.term
  type hol_type = Type.hol_type

  val reserved_prefix : string
  val name_sep : string
  val numeral_prefix : string
  val discr_prefix : string
  val lfp_iterator_prefix : string
  val gfp_iterator_prefix : string
  val skolem_prefix : string
  val uncurry_prefix : string
  val iter_var_prefix : string
  val cyclic_co_val_name : string
  val refute_theory : string
  val funbox_tyop : string
  val pairbox_tyop : string
  val bisim_iterator_tyop : string
  val is_refute_type : string -> hol_type -> bool
  val eval_index : string -> int option
  val strip_first_name_sep : string -> string * string
  val original_name : string -> string
  val sel_prefix_for : int -> string
  val is_sel : string -> bool
  val is_skolem_name : string -> bool
  val is_special_name : string -> bool
  val is_bound_var_name : string -> bool
  val is_cong_var_name : string -> bool
  val sel_no_from_name : string -> int
  val mk_reserved_var : string -> hol_type -> term
  val mk_numeral : int -> hol_type -> term
  val mk_discriminator : string -> hol_type -> term
  val mk_iterator_zero : string -> hol_type -> term
  val mk_iterator_suc : string -> hol_type -> term
  val mk_unrolled : string -> hol_type -> hol_type -> term
  val mk_base : string -> hol_type -> term
  val mk_step : string -> hol_type -> term
  val mk_ubfp : string -> hol_type -> term
  val mk_lbfp : string -> hol_type -> term
  val mk_quot_normal : hol_type -> hol_type -> term
  val is_quot_normal_name : string -> bool
  val is_iterator_zero_name : string -> bool
  val is_iterator_suc_name : string -> bool
  val is_unrolled_name : string -> bool
  val is_base_name : string -> bool
  val is_step_name : string -> bool
  val is_ubfp_name : string -> bool
  val is_lbfp_name : string -> bool
  val mk_selector : int -> string -> hol_type -> term
  val mk_skolem : int -> int -> string -> hol_type -> term
  val mk_special : int -> string -> hol_type -> term
  val mk_bound_var : int -> hol_type -> term
  val mk_cong_var : int -> hol_type -> term
  val mk_eval : int -> hol_type -> term
  val replay_hole_name : int -> string
  val mk_replay_hole : int -> hol_type -> term
  val is_replay_hole_name : string -> bool
  val is_replay_hole : term -> bool
  val unknown_marker : hol_type -> term
  val unrepresented_marker_ascii : hol_type -> term
  val irrelevant_marker : hol_type -> term
  val is_irrelevant_marker : term -> bool
  val contains_irrelevant_marker : term -> bool
  val contains_display_marker : term -> bool
  val rename_irrelevant_collisions :
    term list -> term list * (term * term) list
  val fake_atom : int -> hol_type -> term
  val variable_name : term -> string
  val is_reserved_name : string -> bool
  val reserved_frees : term -> term list
  val assert_user_goal : term -> unit
  val assert_no_reserved_in_theorem : string -> Thm.thm -> unit
  val rename_colliding_goal_vars :
    term list -> term ->
    term * (term * term) list * {redex : hol_type, residue : hol_type} list
end
