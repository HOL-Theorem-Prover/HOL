signature holyHammer =
sig

  include Abbrev
  datatype prover = Eprover | Z3 | Satallax
  
  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)
  
  (* Performs premise selection using the KNN algorithm *)
  val cached_ancfeav : unit ->
    (string, int list) Redblackmap.dict *
    (string * int, string) Redblackmap.dict
  val insert_curfeav : 
    (string, int list) Redblackmap.dict *
    (Dep.depid, string) Redblackmap.dict ->
       (string * int list * string list) list
  val select_premises   : 
    string -> int -> (string * fea_t * string list) list -> term -> 
    (string * string) list
  
  (* Export a problem to TT files *)
  val export_problem    : 
    string -> (string * string) list -> term -> unit
  
  (* Export theories to TT files *)
  val export_theories   : string -> string list -> unit
  
  (* Export and translate a re-proving problem to THF *)
  val reproving_thf      : string -> string * thm -> unit
  val reproving_thf_thyl : string list -> unit
  
  (* Translate the problem from THF to FOF via HOL/Light *)
  val translate_fof     : string -> string -> Process.status
  val translate_thf     : string -> string -> Process.status
  
  (* Calling an automated theorem prover such as "eprover" *)
  val launch_atp        : string -> prover -> int -> Process.status
  
  (* Reconstruct and minimize the proof using Metis *)
  val reconstruct_dir   : string -> term -> tactic
  
  (* Main function and options *)
  val hh_atp            : 
    string -> string -> string -> int -> prover -> int -> term -> tactic
  val holyhammer        : term -> tactic
  val hh_tac            : tactic
  
  (* Holyhammer for Tactictoe with parallel calls *)
  val hh_stac           : 
    int -> (string * fea_t * string list) list ->
    int -> goal -> string option

  (* State *)
  val clean_cache       : unit -> unit
  val set_timeout       : int -> unit
  val set_minimization  : bool -> unit


end
