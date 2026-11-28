(* All ten literal-prefix regressions are normal coverage. *)
val _ = LegacyFailures.start "literal-prefix-contracts";
val _ = List.app
  (fn prefix => List.app
    (fn installed => LegacyFailures.prefix_checks
      {prefix=prefix, installed=installed}) [false,true])
  ["rule:","solver:","looper:","split:","case:"];
val _ = ExclusionHistory.run ();
val _ = ExclusionParsing.run ();
val _ = LegacyFailures.finish ();
