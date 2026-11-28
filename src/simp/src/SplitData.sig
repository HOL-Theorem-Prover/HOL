(* The storage of splitLib's [split] rules.  Loading this module does not
   enable the attribute: splitLib.enable_split_attribute does. *)
signature SplitData =
sig
  datatype raw_delta = Add of KernelSig.kernelname | Remove of string
  val initialize : {validate : Thm.thm -> unit} -> unit
  val exclude : string -> unit
  val named_rules : unit -> (string * Thm.thm) list
  val named_rules_of : Context.t -> (string * Thm.thm) list
  val theory_data : string -> raw_delta list
  val current_data : unit -> raw_delta list
end
