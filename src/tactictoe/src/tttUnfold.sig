signature tttUnfold =
sig

  include Abbrev

  (* tools *)
  val find_script : string -> string
  val unquoteString : string -> string -> string
  val load_sigobj : unit -> unit
  val ttt_rewrite_thy : string -> unit

  (* recording *)
  val ttt_record_thy  : string -> unit
  val ttt_record : unit -> unit
  val ttt_clean_record : unit -> unit

  (* evaluation *)
  val ttt_parallel_eval : int -> string list -> unit 
    (* to be called only after recording the evaluated theories *)
  val evaluate_loaded : string -> int -> unit
  val evaluate_full : string -> int -> unit


end
