signature hhSlice =
sig
  (* How a slice's problem file is written: by the legacy s()/p() FOF
     exporter, or by hhProblemGen with the slice's parsed encoding. *)
  datatype encoding =
      Legacy
    | Generated of {format : hhTptpProblem.format,
                    type_enc : hhTypeEnc.type_enc,
                    lam_trans : hhLamTrans.mode}
  val encoding_of : hhProver.slice -> encoding

  val schedule_of_provers :
    hhProver.prover list -> int -> hhProver.prover list
  val mk_schedule : hhConfig.hh_options ->
    (hhProver.prover_config * hhProver.slice) list
  val filter_maxima :
    (hhProver.prover_config * hhProver.slice) list -> (string * int) list
  val slice_budget : int -> hhConfig.hh_options -> hhProver.slice -> real
end
