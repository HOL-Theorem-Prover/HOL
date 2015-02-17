signature thfWriter =
sig
  
  val fetch_conj : (thm * string) -> thm 
  val write_thf_thyl: string -> string list -> unit
  val write_conjecture: string -> Term.term -> unit
  val replay_atpfilel: string list -> string list -> Term.term -> Thm.thm

end
