signature Globals =
sig

  val HOLDIR                  : string
  val release                 : string
  val version                 : int

  val show_types              : bool ref
  val show_types_verbosely    : bool ref
  val show_numeral_types      : bool ref
  val show_assums             : bool ref
  val show_tags               : bool ref
  val show_axioms             : bool ref
  val show_scrub              : bool ref
  val linewidth               : int ref
  val max_print_depth         : int ref
  val type_pp_prefix          : string ref
  val type_pp_suffix          : string ref
  val term_pp_prefix          : string ref
  val term_pp_suffix          : string ref
  val goal_line               : string ref
  val old                     : string -> string
  val pp_flags                : {show_types         : bool ref,
                                 show_numeral_types : bool ref}

  val priming                 : string option ref
  val guessing_tyvars         : bool ref
  val guessing_overloads      : bool ref
  val notify_on_tyvar_guess   : bool ref
  val allow_schema_definition : bool ref
  val checking_type_names     : bool ref
  val checking_const_names    : bool ref

  val interactive             : bool ref
  val print_thy_loads         : bool ref

  val hol_clock               : Timer.cpu_timer
  val emitMLDir               : string ref
  val emitCAMLDir             : string ref
end
