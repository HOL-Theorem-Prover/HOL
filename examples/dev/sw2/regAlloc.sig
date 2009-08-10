signature regAlloc =
sig
  include Abbrev

  datatype alloc_result
     = Alloc of term (* allocated register *)
     | Spill of term (* spilled variable *)

  val DEBUG : bool ref
  val VarType : hol_type ref
  val numRegs : int ref
  val regL : term list ref
  val reset : unit -> unit
  val parallel_move : term -> term -> term -> term
  val reg_alloc : thm -> thm
  val tvarOrder : term * term -> order
end
