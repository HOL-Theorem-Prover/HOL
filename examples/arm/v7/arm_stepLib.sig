signature arm_stepLib =
sig

  val arm_step : string -> string -> Abbrev.thm

  (*
     usage: arm_step options hex-opcode

     default options: "v7,usr,le,pass,arm,it:0"
  *)

  val step       : HOLFlags.flag
  val step_check : HOLFlags.bflag

end
