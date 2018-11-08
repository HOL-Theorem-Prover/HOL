signature smlExecute =
sig

  include Abbrev

  (* global references used by readers *)
  val sml_bool_glob     : bool ref
  val sml_tacticl_glob  : tactic list ref
  val sml_tactic_glob   : tactic ref
  val sml_qtactic_glob  : (term quotation -> tactic) ref
  val sml_string_glob   : string ref
  val sml_goal_glob     : goal ref
  val sml_term_glob     : term ref
  val sml_termlist_glob : term list ref
  val sml_thm_glob      : thm ref
  val sml_thml_glob     : thm list ref

  (* forward references to metis *)
  val metis_tac_glob   : (thm list -> tactic) option ref
  val update_metis_tac : unit -> unit


  (* execution function *)
  val exec_sml         : string -> string -> bool

  (* test *)
  val is_stype         : string -> bool
  val is_thm           : string -> bool
  val is_tactic        : string -> bool
  val is_string        : string -> bool
  val is_pointer_eq    : string -> string -> bool  

  (* reader *)
  val term_of_sml      : string -> term
  val hol4terml_of_sml  : int -> string -> term list
  val thm_of_sml       : string -> (string * thm) option
  val thml_of_sml      : string list -> (string * thm) list option
  val tactic_of_sml    : string -> tactic
  val qtactic_of_sml   : string -> (term frag list -> tactic)
  val string_of_sml    : string -> string
  val goal_of_sml      : string -> goal

  (* extract theorems from the global namespace *)
  val namespace_thms      : unit -> (string * thm) list
  val safe_namespace_thms : unit -> (string * thm) list


  (* should not be there *)
  val app_tac    : real -> tactic -> goal -> goal list option
  val app_qtac   : real -> (goal -> goal list option) -> goal -> goal list option

  val rec_stac   : real -> string -> goal -> goal list option
  val rec_sproof : string -> goal -> goal list option

  val time_prove: 
    (thm list -> tactic) -> real -> term list -> term -> (term * real) option
  val miniprove : 
    (thm list -> tactic) -> real -> term list -> term -> term list option

end
