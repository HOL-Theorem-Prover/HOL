signature smlParser =
sig

  
  datatype smlexp =
    SmlExp of (string option * string option) * (smlexp list)
  | SmlUnit of (string option * string option)

  datatype proofexp =
    ProofInfix of string * (proofexp * proofexp)
  | ProofTactical of string
  | ProofTactic of string
  | ProofOther of string

  (* parse tree *)
  val parse : string -> PolyML.ptProperties list
  val string_of_propl : PolyML.ptProperties list -> string option

  (* sub expression *)
  val extract_smlexp : string -> smlexp
  val extract_proofexp : string -> proofexp
  val size_of_proofexp : proofexp -> int
  val string_of_proofexp : proofexp -> string

end
