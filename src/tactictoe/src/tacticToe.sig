signature tacticToe =
sig
  
  include Abbrev
  
    (* TacticToe *)
  val ttt : tactic
  val ttt_t : term -> tactic
  
  (* Settings *)
  val set_timeout : real -> unit
  val set_record_hook : (unit -> unit) ref 
    (* flags can only be changed inside this function *)
  
  (* Step by step exploration *)
  val next_tac_glob : tactic list ref
  val next_tac_number : int ref
  val next_tac : goal -> unit 
  val next : int -> tactic  

  (* Recording *)
  val ttt_record : unit -> unit
  val ttt_record_sigobj : unit -> unit
  val ttt_record_thy: string -> unit
  val ttt_clean : unit -> unit
  val ttt_clean_thy: string -> unit
    
  (* Evaluation *)
  val init_tactictoe : unit -> unit (* included in ttt *)
  val eval_tactictoe : string -> goal -> unit
  val ttt_eval_thy: string -> unit
  
end
