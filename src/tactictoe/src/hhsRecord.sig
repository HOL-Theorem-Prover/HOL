signature hhsRecord = 
sig

include Abbrev

  (* Globalizing tactic tokens *)
  val fetch : string -> string -> string
  val name_of_thm : thm -> string

  (* Wrapping tactics *)
  val wrap_tactics_in : string -> string -> tactic
  val record_tactic : (tactic * string) -> tactic
    
  (* Executing the recorder *)
  val set_irecord : unit -> unit
  val set_erecord : unit -> unit
  
  val try_record_proof : string -> bool -> tactic -> tactic -> tactic
  val start_thy : string -> unit
  val end_thy : string -> unit
  
end
