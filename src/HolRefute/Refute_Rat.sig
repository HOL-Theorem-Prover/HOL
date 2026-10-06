signature Refute_Rat = sig
  (* Loading this module installs rational support; register reinstalls it
     in the current context. *)
  val register : unit -> unit
end
