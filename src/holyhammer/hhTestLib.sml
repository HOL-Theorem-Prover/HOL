(* ========================================================================= *)
(* FILE          : hhTestLib.sml                                             *)
(* DESCRIPTION   : Helpers shared by the HolyHammer selftests                *)
(* AUTHOR        : Lukasz Czajka                                             *)
(* ========================================================================= *)

structure hhTestLib =
struct

fun join a b = OS.Path.concat (a, b)

(* smlRedirect redirects fd 1 for the whole process: a redirect that is
   never undone sends every later line to its file while the run goes on
   and succeeds.  check_stdout fails the run, on stderr, when fd 1 is no
   longer the file it was at the start. *)
local
  fun identity () =
    let val status = Posix.FileSys.fstat Posix.FileSys.stdout
    in (Posix.FileSys.ST.dev status, Posix.FileSys.ST.ino status) end
  val initial = identity ()
in
  fun check_stdout context =
    if identity () = initial then ()
    else
      (TextIO.output (TextIO.stdErr,
         "FAILED: stdout is redirected " ^ context ^ "\n");
       TextIO.flushOut TextIO.stdErr;
       OS.Process.exit OS.Process.failure)
end

fun expect message truth =
  (check_stdout ("before \"" ^ message ^ "\"");
   testutils.tprint message;
   if truth then testutils.OK () else testutils.die ("FAILED: " ^ message))

fun expect_equal message expected actual =
  expect message (expected = actual)

(* Runs action with the runtime options settings, then restores the
   runtime values those keys had before, also when action raises. *)
fun with_hh_options settings action =
  let
    val previous = List.mapPartial (fn (key, value, source) =>
      if source = "set" andalso
         List.exists (fn (name, _) => key = name) settings
      then SOME (key, value) else NONE) (hhConfig.hh_params ())
    fun restore () =
      (List.app (hhConfig.hh_unset o #1) settings;
       List.app hhConfig.hh_set previous)
    val _ = List.app hhConfig.hh_set settings
  in
    (action () before restore ())
    handle exn => (restore (); raise exn)
  end

end
