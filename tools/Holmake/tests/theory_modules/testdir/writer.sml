(* Writes the diamond's modules from their .dat files alone, as a module
   store's trusted writer does: WRITER_LIMIT modules at most, into
   "written", using those already in "modules".  Records how many it
   wrote in module-stats. *)
val limit = valOf (Int.fromString (valOf (OS.Process.getEnv "WRITER_LIMIT")));
val written = Meta.writeTheoryModules
  {theories = map (fn t => "module" ^ t ^ "Theory.sml")
                  ["A", "B", "C", "E", "D"],
   directory = "modules", output = "written", limit = limit,
   base_state = OS.Path.concat (Systeml.HOLDIR, "bin/hol.state")};
val out = TextIO.openOut "module-stats";
val _ = TextIO.output (out, Int.toString written);
val _ = TextIO.closeOut out;
