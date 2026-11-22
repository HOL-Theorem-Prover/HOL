(* Stubs for structures that are normally generated at configure time
   or are Poly/ML-specific *)

structure CoreReplVARS =
struct
  val linewidth = ref 72
end

structure Path = OS.Path

(* Poly/ML's value printer, the one `exnMessage' answers from.
   `HOLmessage' registers with it so that a HOL error reports the text
   it was raised with; MLton has no such printer to register with. *)
structure PolyML =
struct
  datatype pretty = PrettyString of string
  fun addPrettyPrinter _ = ()
end
