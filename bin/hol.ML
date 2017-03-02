fun die s =
  (TextIO.output(TextIO.stdErr, s ^ "\n");
   OS.Process.exit OS.Process.failure)

val args = CommandLine.arguments()

fun dropUninteresting l =
  case l of
      "-q" :: rest => dropUninteresting rest
    | "--use" :: file :: rest => dropUninteresting rest
    | "-i" :: rest => dropUninteresting rest
    | gc::rest => if String.isPrefix "--gcthreads" gc then
                    dropUninteresting rest
                  else l
    | _ => l

val realArgs = dropUninteresting args

val (holstate, rest) =
    case realArgs of
        [] => die "No holstate argument provided"
      | x::xs => (x,xs)

val _ = PolyML.SaveState.loadState holstate

val _ = List.app use rest
