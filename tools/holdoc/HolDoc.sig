signature Net_HOLextras = sig

  include Abbrev
  val export_theory : unit -> unit
  val Define : term quotation -> thm
  val xDefine : string -> term quotation -> thm

end;
