signature foobarLib =
sig
  include Abbrev
  (* Add theorem to the foobar set *)
  val add_foobar_thm    : thm -> unit
  (* Query the foobar set for theorems of a given theory *)
  val thy_foobar_thms   : string -> thm list
  (* Get all the theorems in the foobar set *)
  val foobar_thms       : unit   -> thm list
end
