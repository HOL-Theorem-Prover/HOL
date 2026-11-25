(* Reads theory headers the printer breaks (a 59-character theory name),
   headers after more than 4 KiB of opens, and a header with no hash,
   then writes modules from .dat files for a list starting with a theory
   whose header can't be read.  Records in module-stats the headers it
   read and how many modules the writer wrote. *)
val long = "moduleLongNameThatMakesTheGeneratedTheoryHeaderBreakItsLine";
val _ = Meta.configureTheoryModuleCache
          {directory = "modules",
           base_state = OS.Path.concat (Systeml.HOLDIR, "bin/hol.state")};
fun read file =
  let val input = HOLFileSys.openIn file
  in HOLFileSys.inputAll input before HOLFileSys.closeIn input end;
fun write file text =
  let val output = HOLFileSys.openOut file
  in HOLFileSys.output (output, text); HOLFileSys.closeOut output end;
val long_sml = read (long ^ "Theory.sml");
val _ = String.isSubstring "thyname =\n" long_sml orelse
        raise Fail "the long theory name's header line isn't broken";
fun show NONE = "none"
  | show (SOME (thy, hash)) = thy ^ " " ^ Int.toString (size hash);
(* The long theory's source, with 5,000 bytes of opens before its header. *)
val (before_tdb, from_tdb) =
    Substring.position "structure TDB" (Substring.full long_sml);
val _ = write "header-opens.sml"
          (Substring.string before_tdb ^
           String.concat (List.tabulate (250, fn _ => "open Option     \n")) ^
           Substring.string from_tdb);
val _ = write "header-nohash.sml"
          "structure brokenTheory = struct\nval thyname = \"broken\"\nend\n";
val _ = write "brokenTheory.sml" "structure brokenTheory = struct end\n";
val headers =
    map (show o TheoryModules.sml_header)
        [long ^ "Theory.sml", "header-opens.sml", "header-nohash.sml"];
val written = Meta.writeTheoryModules
  {theories = "brokenTheory.sml" ::
              map (fn t => t ^ "Theory.sml")
                  ["moduleA", "moduleB", "moduleC", "moduleE", "moduleD", long],
   directory = "modules", output = "written", limit = 10,
   base_state = OS.Path.concat (Systeml.HOLDIR, "bin/hol.state")};
val _ = app HOLFileSys.remove
          ["header-opens.sml", "header-nohash.sml", "brokenTheory.sml"];
val out = TextIO.openOut "module-stats";
val _ = TextIO.output (out, String.concatWith "\n" headers ^ "\n" ^
                            Int.toString written);
val _ = TextIO.closeOut out;
