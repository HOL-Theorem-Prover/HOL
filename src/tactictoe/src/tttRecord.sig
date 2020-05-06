signature tttRecord =
sig

include Abbrev

  (* These function are printed out by tttUnfold and used in a modified
     fooScript.sml *)

  (* Globalizing tactic tokens *)
  val tacdata_glob : mlTacticData.tacdata ref
  val thmdata_glob : mlThmData.thmdata ref

  val fetch : string -> string -> string
  (* Wrapping tactics *)
  val local_tag : 'a -> 'a
  val wrap_tactics_in : string -> string -> tactic
  val record_tactic : (tactic * string) -> tactic

  (* Executing the recorder *)
  val record_proof : string -> bool -> tactic -> tactic -> tactic
  val start_record_thy : string -> unit
  val end_record_thy : string -> unit

end
