signature tttRecord =
sig

include Abbrev

  (* These functions are printed out by tttUnfold.sml and used in a modified
     fooScript.sml *)

  (* Databases of tactics and theorems *)
  val tacdata_glob : mlTacticData.tacdata ref
  val thmdata_glob : mlThmData.thmdata ref

  (* Globalizing tactic tokens *)
  val fetch : string -> string -> string
  val local_tag : 'a -> 'a

  (* Wrapping proof *)
  val app_wrap_proof : string -> string -> tactic

  (* Executing the wrapped proof *)
  val record_tactic : (tactic * string) -> tactic
  val record_proof : string -> bool -> tactic -> tactic -> tactic

  (* Theory hooks: importing and exporting the tactic database *)
  val start_record_thy : string -> unit
  val end_record_thy : string -> unit

  (* Save state *)
  val savestate_level : int ref
  val ttt_save_state_time : real ref
  val ttt_before_save_state : unit -> unit
  val ttt_save_state : unit -> unit
  val ttt_after_save_state : unit -> unit

  (* Thmdata I/O *)
  val write_thmdata : string -> (string * thm) list -> unit
  val read_thmdata : string -> (string * goal) list

end
