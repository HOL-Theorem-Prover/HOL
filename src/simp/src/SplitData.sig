(* Internal persistence for splitLib. Loading this module claims no public
   namespace and installs no theory-data operations or listeners. *)
signature SplitData =
sig
  datatype raw_delta = Add of KernelSig.kernelname | Remove of string
  val initialize : {validate : Thm.thm -> unit} -> unit
  val exclude : string -> unit
  val named_rules : unit -> (string * Thm.thm) list
  val theory_data : string -> raw_delta list
  val current_data : unit -> raw_delta list
end
