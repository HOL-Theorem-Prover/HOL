(* ========================================================================= *)
(* FILE          : hhTestLib.sml                                             *)
(* DESCRIPTION   : Helpers shared by the HolyHammer selftests                *)
(* AUTHOR        : Lukasz Czajka                                             *)
(* ========================================================================= *)

structure hhTestLib =
struct

fun join a b = OS.Path.concat (a, b)

fun expect message truth =
  (testutils.tprint message;
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
