signature holyHammer =
sig

  include Abbrev
  datatype prover = Eprover | Z3 | Satallax

  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)
  
  (* Read a list of theorems from strings *)
  val thml_of_namel : string list -> (string * thm) list
  
  (* Caching features of theorems *)
  val update_thmdata : unit ->
    (int, real) Redblackmap.dict *
    (string * fea_t) list *
    (string, (goal * int list)) Redblackmap.dict

  (* Export a problem to TT files *)
  val export_problem : string -> string list -> term -> unit

  (* Export theories to TT files *)
  val export_theories : string -> string list -> unit

  (* Translate the problem from THF to FOF via HOL/Light *)
  val translate_fof     : string -> string -> Process.status
  val translate_thf     : string -> string -> Process.status

  (* Calling an automated theorem prover such as "eprover" *)
  val launch_atp        : string -> prover -> int -> Process.status

  (* Reconstruct and minimize the proof using Metis *)
  val reconstruct_dir   : string -> goal -> tactic

  (* Main function and options *)
  val holyhammer_pb     : string list -> goal -> tactic
  val holyhammer        : term -> tactic
  val hh                : tactic

  (* Holyhammer for Tactictoe with parallel calls *)
  val hh_stac           :
    string ->
      (int, real) Redblackmap.dict *
      (string * fea_t) list *
      (string, (goal * int list)) Redblackmap.dict
    -> int -> goal -> string option
  
  (* Exporting fof problems *)
  val create_fof        : string -> thm -> unit

  (* State *)
  val clean_cache       : unit -> unit
  val set_timeout       : int -> unit
  
  (* New holyhammer *)
  val hh_pb : string list -> goal -> tactic
  val hh_new_goal : goal -> tactic
  val hh_new : term -> tactic

end
