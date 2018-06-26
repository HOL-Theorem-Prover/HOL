signature stack_analysisLib =
sig

  val get_pc_pat : unit -> Term.term
  val find_stack_accesses :
     string ->
       (int * (Thm.thm * int * int option) *
              (Thm.thm * int * int option) option) list -> int list

end
