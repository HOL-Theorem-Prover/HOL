(*  Title:      Pure/General/exn.ML
    Author:     Makarius

Support for exceptions.
*)

signature Exn =
sig
  exception ERROR of string
  val error: string -> 'a
  val cat_error: string -> string -> 'a
  val polyml_location: exn -> PolyML.location option
  val reraise: exn -> 'a
  datatype 'a result = Res of 'a | Exn of exn
  val get_res: 'a result -> 'a option
  val get_exn: 'a result -> exn option
  val capture: ('a -> 'b) -> 'a -> 'b result
  val release: 'a result -> 'a
  val map_res: ('a -> 'b) -> 'a result -> 'b result
  val maps_res: ('a -> 'b result) -> 'a result -> 'b result
  val map_exn: (exn -> exn) -> 'a result -> 'a result
  exception Interrupt
  val interrupt: unit -> 'a
  val is_interrupt: exn -> bool
  val interrupt_exn: 'a result
  val is_interrupt_exn: 'a result -> bool
  val interruptible_capture: ('a -> 'b) -> 'a -> 'b result
  exception EXCEPTIONS of exn list
  val trace: (exn -> string) -> (string -> unit) -> (unit -> 'a) -> 'a
end
