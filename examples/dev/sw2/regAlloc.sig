signature regAlloc =
sig
  include Abbrev

  datatype alloc_result 
     = Alloc of term (* allocated register *)
     | Spill of term (* spilled variable *)

  val DEBUG : bool ref
  val numRegs : int ref
  val regL : term list ref
  val reset : unit -> unit
  val reg_alloc : thm -> thm
end
