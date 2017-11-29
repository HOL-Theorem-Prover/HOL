signature machine_ieeeSyntax =
sig
  val fp16_to_fp32_tm: Term.term
  val fp16_to_fp64_tm: Term.term
  val fp32_to_fp64_tm: Term.term
  val fp64_to_fp32_tm: Term.term
  val fp64_to_fp16_tm: Term.term
  val fp32_to_fp16_tm: Term.term
  val fp16_to_fp32_with_flags_tm: Term.term
  val fp16_to_fp64_with_flags_tm: Term.term
  val fp32_to_fp64_with_flags_tm: Term.term
  val fp64_to_fp32_with_flags_tm: Term.term
  val fp64_to_fp16_with_flags_tm: Term.term
  val fp32_to_fp16_with_flags_tm: Term.term

  val mk_fp16_to_fp32: Term.term -> Term.term
  val mk_fp16_to_fp64: Term.term -> Term.term
  val mk_fp32_to_fp64: Term.term -> Term.term
  val mk_fp64_to_fp32: Term.term * Term.term -> Term.term
  val mk_fp64_to_fp16: Term.term * Term.term -> Term.term
  val mk_fp32_to_fp16: Term.term * Term.term -> Term.term
  val mk_fp16_to_fp32_with_flags: Term.term -> Term.term
  val mk_fp16_to_fp64_with_flags: Term.term -> Term.term
  val mk_fp32_to_fp64_with_flags: Term.term -> Term.term
  val mk_fp64_to_fp32_with_flags: Term.term * Term.term -> Term.term
  val mk_fp64_to_fp16_with_flags: Term.term * Term.term -> Term.term
  val mk_fp32_to_fp16_with_flags: Term.term * Term.term -> Term.term

  val dest_fp16_to_fp32: Term.term -> Term.term
  val dest_fp16_to_fp64: Term.term -> Term.term
  val dest_fp32_to_fp64: Term.term -> Term.term
  val dest_fp64_to_fp32: Term.term -> Term.term * Term.term
  val dest_fp64_to_fp16: Term.term -> Term.term * Term.term
  val dest_fp32_to_fp16: Term.term -> Term.term * Term.term
  val dest_fp16_to_fp32_with_flags: Term.term -> Term.term
  val dest_fp16_to_fp64_with_flags: Term.term -> Term.term
  val dest_fp32_to_fp64_with_flags: Term.term -> Term.term
  val dest_fp64_to_fp32_with_flags: Term.term -> Term.term * Term.term
  val dest_fp64_to_fp16_with_flags: Term.term -> Term.term * Term.term
  val dest_fp32_to_fp16_with_flags: Term.term -> Term.term * Term.term

  val is_fp16_to_fp32: Term.term -> bool
  val is_fp16_to_fp64: Term.term -> bool
  val is_fp32_to_fp64: Term.term -> bool
  val is_fp64_to_fp32: Term.term -> bool
  val is_fp64_to_fp16: Term.term -> bool
  val is_fp32_to_fp16: Term.term -> bool
  val is_fp16_to_fp32_with_flags: Term.term -> bool
  val is_fp16_to_fp64_with_flags: Term.term -> bool
  val is_fp32_to_fp64_with_flags: Term.term -> bool
  val is_fp64_to_fp32_with_flags: Term.term -> bool
  val is_fp64_to_fp16_with_flags: Term.term -> bool
  val is_fp32_to_fp16_with_flags: Term.term -> bool
end
