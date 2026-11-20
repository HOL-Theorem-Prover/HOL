(* Lambda translation for the new HolyHammer problem generator. *)
signature hhLamTrans =
sig

  type term = Term.term

  (* The slice vocabulary names the modes lifting, combs,
     combs_and_lifting and keep_lams.  The empty string denotes the legacy
     exporter and is deliberately rejected here.  The problem generator,
     rather than this module, downgrades keep_lams to lifting for formats
     without full HO syntax. *)
  datatype mode = Lifting | Combs | CombsAndLifting | KeepLams
  val mode_of_string : string -> mode
  val mode_name : mode -> string
  val valid_mode : string -> bool
  val translate :
    mode -> term list -> term list * (string * term) list
  (* mode -> formulas -> (rewritten formulas, named lambda definitions) *)

end
