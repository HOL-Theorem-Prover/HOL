fun die s =
  (TextIO.output(TextIO.stdErr, s ^ "\n");
   OS.Process.exit OS.Process.failure)

val args = CommandLine.arguments()

(* Flags that must survive loadState — they are set after heap restore below.
   These Globals refs are clobbered by loadState back to saved-heap values,
   so we extract them from args before identifying the holstate, then set them
   after loadState. *)
val dumpheap_flag = ref false
val g_flag = ref false
val allow_cheat_flag = ref false
val tactic_timeout_val = ref 0.0

fun extractHolmakeFlags l =
  case l of
      "--dumpheap" :: rest =>
        (dumpheap_flag := true; extractHolmakeFlags rest)
    | "-g" :: rest =>
        (g_flag := true; extractHolmakeFlags rest)
    | "--allow-cheat" :: rest =>
        (allow_cheat_flag := true; extractHolmakeFlags rest)
    | s :: rest =>
        if String.isPrefix "--tactic-timeout=" s then (
          tactic_timeout_val :=
            Option.getOption (Real.fromString (String.extract (s, 17, NONE)), 0.0);
          extractHolmakeFlags rest
        ) else s :: extractHolmakeFlags rest
    | [] => []

fun dropUninteresting l =
  case l of
      "-q" :: rest => dropUninteresting rest
    | "--use" :: file :: rest => dropUninteresting rest
    | "-i" :: rest => dropUninteresting rest
    | "--maxheap" :: _ :: rest => dropUninteresting rest
    | gc::rest => if String.isPrefix "--gcthreads" gc then
                    dropUninteresting rest
                  else l
    | _ => l

val realArgs = dropUninteresting (extractHolmakeFlags args)

val (holstate, rest) =
    case realArgs of
        [] => die "No holstate argument provided"
      | x::xs => (x,xs)

val _ = PolyML.SaveState.loadState holstate

(* Set Globals AFTER loadState — the heap restore clobbers all ref values *)
val _ = Globals.holmake_dumpheap_flag := !dumpheap_flag
val _ = Globals.holmake_g_flag := !g_flag
val _ = Globals.holmake_allow_cheat := !allow_cheat_flag
val _ = Globals.holmake_tactic_timeout := !tactic_timeout_val

val _ = List.app use rest
