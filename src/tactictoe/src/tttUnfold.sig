signature tttUnfold =
sig

  include Abbrev

  (* tools *)
  val find_script : string -> string
  val unquoteString : string -> string -> string
  val load_sigobj : unit -> unit

  (* recording *)
  val ttt_rewrite_thy : string -> unit
  val ttt_record_thy  : string -> unit
  val ttt_rewrite : unit -> string list
  val ttt_record : unit -> unit (* includes ttt_rewrite *)

end
