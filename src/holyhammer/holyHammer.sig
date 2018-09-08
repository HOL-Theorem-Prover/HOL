signature holyHammer =
sig

  include Abbrev
  datatype prover = Eprover | Z3 | Vampire

  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)
  
  (* Directories *)
  val hh_dir : string
  val hh_eval_dir : string
  
  (* Settings *)
  val set_timeout        : int -> unit
  val all_atps           : prover list ref 
    (* atps called by holyhammer if their binary exists *)
  
  (* Read theorems from their string representataion *)
  val thml_of_namel : string list -> (string * thm) list
  
  (* Caching features of goals *)
  val clean_goalfea_cache : unit -> unit
  
  (* Updating the database of theorems *)
  val update_thmdata : unit ->
    (int, real) Redblackmap.dict *
    (string * fea_t) list *
    (string, (goal * int list)) Redblackmap.dict
  
  (* Calling an automated theorem prover such as "eprover" *)
  val launch_atp        : string -> prover -> int -> string list option

  (* Reconstruct and minimize the proof using Metis *)
  val hh_reconstruct    : string list -> goal -> (string * tactic)

  (* Main functions *)
  val hh_pb             : prover list -> string list -> goal -> tactic
  val clean_goaltac_cache : unit -> unit 
    (* saving results of the next functions in goaltac_cache *)
  val hh_goal           : goal -> tactic
  val hh_fork           : goal -> Thread.thread
  val holyhammer        : term -> tactic
  val hh                : tactic
  
  (* Other functions *)
  val metis_auto        : real -> int -> goal -> string option
  
  (* For tttSyntEval.sml *)
  val export_pb : 
    string -> int -> term list * term -> 
    int * (term * (string, term) Redblackmap.dict)
  val eprover_parallel: 
    string -> int -> int list -> int -> 
    (int * string list option) list



  (* HolyHammer for TacTicToe parallel calls *)
  val hh_stac           :
    string ->
      (int, real) Redblackmap.dict *
      (string * fea_t) list *
      (string, (goal * int list)) Redblackmap.dict
    -> int -> goal -> string option
 
  (* Evaluation *)
  val hh_eval_thm : prover list -> bool -> (string * thm) -> unit
  val hh_eval_thy : prover list -> bool -> string -> unit

  (* Export HOL4 library to Holyhammer infrastructure in HOL/Light *)
  val export_problem  : string -> string list -> term -> unit
  val export_theories : string -> string list -> unit
  
end
