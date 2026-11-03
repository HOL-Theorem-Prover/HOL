open testutils;

val _ = OS.FileSys.chDir "testdir";
val hol = OS.Path.concat (Systeml.HOLDIR, "bin/hol");
val holmake = OS.Path.concat (Systeml.HOLDIR, "bin/Holmake");

fun command args =
  if OS.Process.isSuccess (Systeml.systeml args) then ()
  else die (String.concatWith " " args);
fun read path =
  let val input = HOLFileSys.openIn path
  in HOLFileSys.inputAll input before HOLFileSys.closeIn input end;
fun remove path = OS.FileSys.remove path handle OS.SysErr _ => ();
fun children directory =
  let
    val input = OS.FileSys.openDir directory
    fun loop () =
      case OS.FileSys.readDir input of
          NONE => []
        | SOME name => name :: loop ()
  in
    loop () before OS.FileSys.closeDir input
  end;
fun clear directory =
  (app (fn name => remove (OS.Path.concat (directory, name)))
       (children directory);
   OS.FileSys.rmDir directory) handle OS.SysErr _ => ();
fun probe () = command [hol, "run", "--noconfig", "probe.sml"];
fun outputs () = map (read o (fn ext => "moduleProbeTheory." ^ ext))
                     ["dat", "sig", "sml"];
fun stats () = List.mapPartial Int.fromString
                (String.tokens Char.isSpace (read "module-stats"));
fun misses () = case stats () of [_,n,_] => n | _ => 0;

val _ = command [holmake, "--no-cache", "cleanAll"];
val _ = command [holmake, "--no-cache", "moduleDTheory.uo"];
val _ = clear "modules";
val _ = clear "producer-modules";
val _ = remove "module-stats";
val _ = tprint "source theory load preserves kernel identity and diamond hooks";
val _ = probe ();
val cold = outputs ();
val _ = OK ();

(* Stock Poly/ML still checks the generated source path. *)
val supported = OS.FileSys.access ("module-stats", []);
val _ = if not supported then () else
  let
    val _ = tprint "compiled initializer replays registration and hooks"
    val _ = probe ()
    val _ = if stats () = [4,0,0] andalso outputs () = cold then OK ()
            else die "warm module load changed state or theory outputs"
    val _ = tprint "factory production does not reload a sealed export"
    val _ = if List.exists (String.isSuffix ".ref")
                           (children "producer-modules") then OK ()
            else die "exported theory factory was not produced"
    val _ = tprint "missing module payload falls back to source"
    val reference = hd (List.filter (String.isSuffix ".ref")
                                   (children "modules"))
    val payload = OS.Path.concat
                    ("modules", read (OS.Path.concat ("modules", reference)) ^
                                ".pmo")
    val _ = remove payload
    val _ = probe ()
    val _ = if outputs () = cold andalso misses () > 0 then OK ()
            else die "missing-module fallback changed results"
    val _ = tprint "corrupt module payload is rejected before native loading"
    val current_payload = OS.Path.concat
      ("modules", read (OS.Path.concat ("modules", reference)) ^ ".pmo")
    val output = TextIO.openOut current_payload
    val _ = TextIO.output (output, "corrupt") before TextIO.closeOut output
    val _ = probe ()
    val _ = if outputs () = cold andalso misses () > 0 then OK ()
            else die "corrupt-module fallback changed results"
    val _ = tprint "changed theory source ignores the old compiled initializer"
    val output = HOLFileSys.openAppend "moduleATheory.sml"
    val _ = TextIO.output (output, "\n(* changed source *)\n")
              before TextIO.closeOut output
    val _ = probe ()
    val _ = if outputs () = cold andalso misses () = 1 then OK ()
            else die "stale-module fallback changed results"
    val _ = tprint "changed core ML binding forces source initialization"
    val _ = command ["env", "HOL_MODULE_TEST_SHADOW=1", hol,
                     "run", "--noconfig", "probe.sml"]
    val _ = if outputs () = cold andalso misses () > 0 then OK ()
            else die "changed-namespace fallback changed results"
  in
    ()
  end;
val _ = clear "modules";
val _ = clear "producer-modules";
val _ = remove "module-stats";
val _ = command [holmake, "--no-cache", "cleanAll"];
