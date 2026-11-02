signature Refute_EvalRat = sig
  val generator : Refute_Gen.custom_gen
  val register : unit -> unit
end
