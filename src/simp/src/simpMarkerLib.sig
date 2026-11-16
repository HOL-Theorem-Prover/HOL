(* The extension simplifier's directives, Split and ExclX, alongside
   markerLib's *)
signature simpMarkerLib =
sig
  include Abbrev
  val Split_tm : term
  val Split : thm -> thm
  val destSplit : thm -> thm
  val ExclX : string -> thm
  val destExclX : thm -> string option
  datatype directive =
    Legacy of markerLib.directive | DSplit of thm | DExclX of string
  val dest_directive : thm -> directive option
  val is_directive : thm -> bool
  val strip_wrappers : thm -> thm
  (* As markerLib.process_taclist_then, but the continuation is also given
     a function that selects the assumptions again in the same way, for
     later goals (e.g. a looper's).  The list's tactics and requirement
     checks run only once. *)
  val process_taclist_then_recur : {arg : thm list} ->
    (((thm list -> tactic) -> tactic) -> thm list -> tactic) -> tactic
  (* As process_taclist_then_recur, but the continuation is given the
     theorem arguments and the selected assumptions separately, so that
     it can prepare the arguments once. *)
  val process_taclist_then_bind : {arg : thm list} ->
    (thm list -> ((thm list -> tactic) -> tactic) -> thm list -> tactic) ->
    tactic
end
