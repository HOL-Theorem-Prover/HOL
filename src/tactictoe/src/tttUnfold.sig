signature tttUnfold =
sig

  include Abbrev

  (* tools *)
  val find_script : string -> string
  val load_sigobj : unit -> unit
  val ttt_rewrite_thy : string -> unit

  (* recording *)
  val ttt_record_thy  : string -> unit
  val ttt_record : unit -> unit
  val ttt_clean_record : unit -> unit

end
