signature computeLib =
sig

  local open HolKernel Abbrev in

  type rewrite = clauses.rewrite
  type comp_rws = clauses.comp_rws

  val new_rws : unit -> comp_rws
  val from_list : bool -> thm list -> comp_rws
  val add_clauses : bool -> thm list -> comp_rws -> rewrite list

  val CBV_CONV      : comp_rws -> conv
  val WEAK_CBV_CONV : comp_rws -> conv

  end

end;
