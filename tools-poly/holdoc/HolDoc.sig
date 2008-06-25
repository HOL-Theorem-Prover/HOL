signature HolDoc = sig

(*

  Code to automatically generate .imn information for theories at
  export time.  Output is in file <thyname>.imn.

  To get this to work it must be the last module opened (more
  accurately, it must override bossLib and HolKernel, and so must
  follow these two).

*)

  include Abbrev
  val export_theory : unit -> unit
  val Define : term quotation -> thm
  val xDefine : string -> term quotation -> thm

end;
