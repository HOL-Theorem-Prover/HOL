(* ===================================================================== *)
(* FILE          : Globals.sig                                           *)
(* DESCRIPTION   : Signature for global flags.                           *)
(*                                                                       *)
(* AUTHOR        : Ken Larsen, University of Cambridge                   *) 
(*                 Based on globals.sig by                               *)
(*                 (c) Konrad Slind, University of Calgary               *)
(* DATE          : September 22, 1997                                    *)
(* ===================================================================== *)


signature Globals =
sig

  val release : string
  val version : int
  val HOLDIR  : string

  val print_exceptions : bool ref
  val show_assums      : bool ref
  val show_tags        : bool ref
  val show_axioms      : bool ref
  val show_scrub       : bool ref

  val show_dB          : bool ref
  val show_restrict    : bool ref
  val show_types       : bool ref
  val infix_at_front   : bool ref
  val stack_infixes    : bool ref
  val in_at_end        : bool ref

  val priming          : string option ref
  val guessing_tyvars  : bool ref
  val notify_on_tyvar_guess : bool ref

  val linewidth        : int ref
  val max_print_depth  : int ref

  val type_pp_prefix   : string ref
  val type_pp_suffix   : string ref
  val term_pp_prefix   : string ref
  val term_pp_suffix   : string ref
  val goal_line        : string ref

  val old              : (string -> string) ref
  val in_type_spec     : string option ref
  val tilde_symbols    : string list ref

  val output_HOL_ERR   : ({origin_structure : string,
                           origin_function : string,
  		           message : string} -> unit) ref

  val pp_flags : {show_dB: bool ref,
                  show_restrict:bool ref,
                  show_types: bool ref,
                  infix_at_front:bool ref,
                  stack_infixes :bool ref,
                  in_at_end : bool ref}

  val reserved_identifiers : {symbolic : string list, 
                              alphanumeric : string list}

  val neg_defined            : unit -> bool
  val nums_defined           : unit -> bool
  val strings_defined        : unit -> bool
  val assert_neg_defined     : unit -> unit
  val assert_nums_defined    : unit -> unit
  val assert_strings_defined : unit -> unit

end
