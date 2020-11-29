signature tttUnfold =
sig

  include Abbrev

  (* tools *)
  val find_script : string -> string
  val load_sigobj : unit -> unit
  val ttt_rewrite_thy : string -> unit

  (* recording tactic data *)
  val ttt_record_thy  : string -> unit
  val ttt_clean_record : unit -> unit
  val ttt_record : unit -> unit

  (* creating savestates before each proof 
     (requires some flags see usage in tttEval) *)
  val ttt_clean_savestate : unit -> unit
  val ttt_record_savestate : unit -> unit

end
