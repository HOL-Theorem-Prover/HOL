signature tttEval =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn
  type nnfiles = string option * string option * string option

  val oldeval_flag : bool ref
  val is_oldeval : string -> bool

  (* holyhammer function for the evaluation framework *)
  val cheat_flag : bool ref
  val hh_flag : bool ref
  val hh_glob : (string -> mlThmData.thmdata -> goal -> tactic) option ref
  val hh_timeout : int ref
  val import_hh : 
    unit -> (string -> mlThmData.thmdata -> goal -> tactic) option
  
  (* tnn examples *)
  val collect_ex : string -> ((term * real list) list) list
  val uniq_ex : ((term * real list) list) list -> ((term * real list) list) list
  val tnnex_to_basicex : ((term * real list) list) list -> (term * real) list
  
  (* tactictoe function for the evaluation framework *)
  val prepare_global_data : (string * int) -> unit
  val ttt_eval : string -> (string * int) -> 
    mlThmData.thmdata * mlTacticData.tacdata ->
    tnn option * tnn option * tnn option ->
    goal -> unit

  (* running evaluation framework *)
  val write_evalscript : string -> string -> nnfiles -> string -> unit
  val run_evalscript : string -> string -> nnfiles -> string -> unit
  val run_evalscript_thyl : string -> string -> bool * int ->
    nnfiles -> string list -> unit
  val run_evalscript_filel : string -> string -> bool * int ->
    nnfiles -> string list -> unit

  (* statistics after evaluation *)
  val compile_info : string -> string
  val proofl_exp : string -> (string * real) list

  (* reinforcement learning for the value *)
  val rlval : int -> string -> string list -> int -> unit
  val rlval_loop: int -> string -> string list -> int * int -> unit

end
