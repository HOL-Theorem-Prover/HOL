signature regexpLib =
sig

  include Abbrev
  type regexp = Regexp_Type.regexp

  datatype evaluator = HOL | SML

  val gen_dfa_conv : regexp -> thm * thm

  val gen_dfa : evaluator
                  -> regexp
                  -> {table:int vector vector,
                      start:int,
                      final:bool vector,
                      matchfn : string -> bool,
                      certificate: thm option,
                      aux : thm option}

  val dfa_by_proof : string * regexp -> thm

  val charset_conv_ss : simpLib.ssfrag

end
