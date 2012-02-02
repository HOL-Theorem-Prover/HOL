(* Copyright (c) 2010-2011 Tjark Weber. All rights reserved. *)

signature HolQbfLib = sig

  val prove         : Term.term -> Thm.thm
  val disprove      : Term.term -> Thm.thm
  val decide_prenex : Term.term -> Thm.thm
  val decide        : Term.term -> Thm.thm
  (* Default sat solver is HolSatLib.SAT_PROVE *)
  val set_sat_prove : (Term.term -> Thm.thm) -> unit

end
