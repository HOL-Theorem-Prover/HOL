signature tttRecord =
sig

include Abbrev

  (* Globalizing tactic tokens *)
  val fetch : string -> string -> string

  (* Wrapping tactics *)
  val local_tag : 'a -> 'a
  val wrap_tactics_in : string -> string -> tactic
  val record_tactic : (tactic * string) -> tactic

  (* Executing the recorder *)
  val try_record_proof :
    string -> bool -> tactic -> tactic -> tactic
  val start_record : string -> unit
  val end_record : string -> unit

end
