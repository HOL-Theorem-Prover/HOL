signature computeLib =
sig

  type term = Term.term

  type comp_rws = clauses.comp_rws

  val new_rws : unit -> comp_rws
  val from_list : Thm.thm list -> comp_rws
  val add_thms : Thm.thm list -> comp_rws -> unit
  val add_conv : term * int * Abbrev.conv -> comp_rws -> unit
  val set_skip : comp_rws -> string -> int option -> unit

  val CBV_CONV      : comp_rws -> Abbrev.conv
  val WEAK_CBV_CONV : comp_rws -> Abbrev.conv

  (* Thm.thm preprocessors of rules.sml *)
  val lazyfy_thm    : Thm.thm -> Thm.thm
  val strictify_thm : Thm.thm -> Thm.thm


end;
