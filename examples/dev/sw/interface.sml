structure interface = struct

  structure IR = annotatedIL

  val compile_ir =  funCall.link_ir
  val sfl2ir = IR.sfl2ir
  val printIR = IR.printIR
  val printIR2 = IR.printIR2

(*
  val pp_compile = pp_compile;
  val get_spec = get_spec;
  val f_correct = f_correct;
*)

end
