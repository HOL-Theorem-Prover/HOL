signature tttExec =
sig

  include Abbrev

  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)

  val ttt_bool_glob    : bool ref
  val ttt_tacticl_glob : tactic list ref
  val ttt_tactic_glob  : tactic ref
  val ttt_qtactic_glob : (term quotation -> tactic) ref
  val ttt_string_glob  : string ref
  val ttt_goal_glob    : goal ref
  
  (* forward references to holyhammer and metis *)
  val hh_stac_glob     :
    (string ->
       (int, real) Redblackmap.dict *
       (string * fea_t) list *
       (string, goal * int list) Redblackmap.dict ->
     int -> goal -> string option) ref
  val update_hh_stac   : unit -> unit
  val metis_tac_glob   : (thm list -> tactic) option ref
  val update_metis_tac : unit -> unit

  val create_fof_glob   : (string -> thm -> unit) ref
  val update_create_fof : unit -> unit
  
  (* execution function *)
  val exec_sml         : string -> string -> bool

  val ttt_term_glob    : term ref
  val ttt_termlist_glob : term list ref
  val is_stype         : string -> bool
  val term_of_sml      : string -> term
  val hol4terml_of_sml  : int -> string -> term list
  val ttt_thm          : thm ref
  val ttt_thml         : thm list ref
  val is_thm           : string -> bool
  val thm_of_sml       : string -> (string * thm) option
  val thml_of_sml      : string list -> (string * thm) list option

  val smltype_of_value :
    (string * PolyML.NameSpace.Values.value) list -> string -> string
  val is_thm_value     :
    (string * PolyML.NameSpace.Values.value) list -> string -> bool

  val namespace_thms      : unit -> (string * thm) list
  val safe_namespace_thms : unit -> (string * thm) list

  val is_tactic        : string -> bool
  val is_string        : string -> bool
  val is_pointer_eq    : string -> string -> bool

  val tactic_of_sml    : string -> tactic
  val qtactic_of_sml   : string -> (term frag list -> tactic)
  val string_of_sml    : string -> string
  val goal_of_sml      : string -> goal


  val app_tac    : real -> tactic -> goal -> goal list option
  val app_qtac    : real -> (goal -> goal list option) -> goal -> goal list option

  val rec_stac   : real -> string -> goal -> goal list option
  val rec_sproof : string -> goal -> goal list option

  (* prover *)
  val time_mprove: 
    (thm list -> tactic) -> real -> term list -> term -> (term * real) option
  val miniprove : 
    (thm list -> tactic) -> real -> term list -> term -> term list option

end
