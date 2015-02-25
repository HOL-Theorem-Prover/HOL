signature thfWriter =
sig
  
  val fetch_conj       : (thm * string) -> thm 
  val write_thf_thyl   : string -> string list -> unit
  val write_conjecture : string -> Term.term -> unit
  val write_thydep     : string -> string list -> unit
  val replay_atpfile   : (string * string) -> Term.term -> Thm.thm
  val replay_atpfilel  : (string * string) list -> Term.term -> Thm.thm
  val minimize_flag    : bool ref
  val minimize         :
      ({Name: string, Thy: string} * Dep.depchoice list) list ->
        term -> ({Name: string, Thy: string} * Dep.depchoice list) list

end
