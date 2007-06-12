signature regAlloc =
sig
  include Abbrev

  datatype alloc_result 
     = Alloc of term (* allocated register *)
     | Spill of term (* spilled variable *)

  val DEBUG : bool ref
  val allregs : term list
  val reg_sp : term
  val reg_hp : term
  val regL : term list ref
  val alloc_mem : term -> term
  val reg_alloc : thm -> thm
end
