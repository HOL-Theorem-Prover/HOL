signature checkRegressions =
sig

  (* `logsuffix' is the tail of the log names to draw baselines from -
     kernel and selftest level together, as `finish_logging' wrote it,
     e.g. "-stdknl-t3". *)
  val run : {logdir : string, latest : string, logsuffix : string} -> unit

end
