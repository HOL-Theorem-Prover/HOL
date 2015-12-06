signature machine_ieeeSyntax =
sig
  structure fp16Syntax : fpSyntax
  structure fp32Syntax : fpSyntax
  structure fp64Syntax : fpSyntax

  val fp32_to_fp64_tm: Term.term
  val fp64_to_fp32_tm: Term.term

  val mk_fp32_to_fp64: Term.term -> Term.term
  val mk_fp64_to_fp32: Term.term * Term.term -> Term.term

  val dest_fp32_to_fp64: Term.term -> Term.term
  val dest_fp64_to_fp32: Term.term -> Term.term * Term.term

  val is_fp32_to_fp64: Term.term -> bool
  val is_fp64_to_fp32: Term.term -> bool
end
