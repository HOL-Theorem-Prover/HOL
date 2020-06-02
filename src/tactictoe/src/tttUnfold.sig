signature tttUnfold =
sig

  include Abbrev

  (* tools *)
  val unquote_sml : string -> string
  val find_script : string -> string
  val unquote_script : string -> string -> string
  val load_sigobj : unit -> unit
  val ttt_rewrite_thy : string -> unit

  (* recording *)
  val ttt_record_thy  : string -> unit
  val ttt_record : unit -> unit
  val ttt_clean_record : unit -> unit

  (* evaluation *)
  val write_evalscript : string -> string -> unit
  val run_evalscript : string -> string -> unit
  val run_evalscript_thyl : string -> bool -> int -> string list -> unit

end
