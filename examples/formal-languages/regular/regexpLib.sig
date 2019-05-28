signature regexpLib =
sig

  include Abbrev
  type regexp = Regexp_Type.regexp

  val regexp_compset : unit -> computeLib.compset

  datatype evaluator = HOL | SML

  val matcher : evaluator
                  -> regexp
                  -> {table:int vector vector,
                      start:int,
                      final:bool vector,
                      matchfn : string -> bool,
                      certificate: thm option}

  val dfa_by_proof : string * regexp -> thm

  val charset_conv_ss : simpLib.ssfrag

end
