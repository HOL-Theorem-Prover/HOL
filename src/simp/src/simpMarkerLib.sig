(* Simplifier directives: legacy classification remains in markerLib. *)
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
  (* Run pretactics and requirement checks once; recursive passes reapply
     the saved assumption policy and pass the stripped arguments. *)
  val process_taclist_then_recur : {arg : thm list} ->
    (((thm list -> tactic) -> tactic) -> thm list -> tactic) -> tactic
  (* Bind supplied facts once after pretactics succeed, then select
     assumptions afresh per pass. Resolve labels before pretactics and
     decode wrapper-qualified tactic options before classification. *)
  val process_taclist_then_bind : {arg : thm list} ->
    (thm list -> ((thm list -> tactic) -> tactic) -> thm list -> tactic) ->
    tactic
end
