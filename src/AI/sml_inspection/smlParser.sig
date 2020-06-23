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

  datatype applyexp =
    ApplyExp of applyexp * applyexp
  | ApplyUnit of (string * string option)

  (* parse tree *)
  val parse : string -> PolyML.ptProperties list
  val string_of_propl : PolyML.ptProperties list -> string option

  (* sub expression *)
  val extract_smlexp : string -> smlexp
  
  (* proof expression *)
  val extract_proofexp : smlexp -> proofexp
  val size_of_proofexp : proofexp -> int
  val string_of_proofexp : proofexp -> string

  (* apply expression *)
  val extract_applyexp : smlexp -> applyexp

end
