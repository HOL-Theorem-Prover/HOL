(* Copyright (c) 2010 Tjark Weber. All rights reserved. *)

signature HolQbfLib = sig

  val prove    : Term.term -> Thm.thm
  val disprove : Term.term -> Thm.thm
  val decide   : Term.term -> Thm.thm

end
