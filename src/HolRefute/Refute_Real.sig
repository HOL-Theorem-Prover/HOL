signature Refute_Real = sig
  (* Loading this module installs real support; register reinstalls it
     in the current context. *)
  val register : unit -> unit
end
