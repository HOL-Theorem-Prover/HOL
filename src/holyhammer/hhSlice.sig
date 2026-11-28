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

  (* schedule_of_provers provers count: the provers of count slices, in
     portfolio order while it lasts, then round robin over provers. *)
  val schedule_of_provers :
    hhProver.prover list -> int -> hhProver.prover list
  (* The slices of the requested provers' tables, each prover's next one
     at its turn in schedule_of_provers (for the built-in tables, portfolio
     order), with the option overrides applied and duplicates dropped: at
     most the slices option of them.  Raises Fail on a slice its prover
     cannot run. *)
  val mk_schedule : hhConfig.hh_options ->
    (hhProver.prover_config * hhProver.slice) list
  (* Each distinct filter of a schedule in first-use order, with its
     largest fact count. *)
  val filter_maxima :
    (hhProver.prover_config * hhProver.slice) list ->
    (hhConfig.premise_filter * int) list
  (* slice_budget schedule_length options slice: the seconds slice gets,
     slice_size times the timeout over the number of batches of cores
     slices in the schedule. *)
  val slice_budget : int -> hhConfig.hh_options -> hhProver.slice -> real
end
