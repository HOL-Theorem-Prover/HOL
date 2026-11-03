signature Refute_EvalCompute = sig
  type term = Term.term

  val fraction_generator : (int * int -> term) -> Refute_Gen.custom_gen
  val register_substrate : unit -> unit
end
