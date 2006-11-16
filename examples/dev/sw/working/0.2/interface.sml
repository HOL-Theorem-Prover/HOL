structure interface = struct

  structure IR = annotatedIR

  val compile_ir =  funCall.link_ir
  val sfl2ir = IR.sfl2ir
  val printIR = IR.printIR
  val printIR2 = IR.printIR2
  (*
  val pp_compile = mechReasoning.pp_compile;
  *)
end
