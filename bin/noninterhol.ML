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

val holstate =
    case dropUninteresting args of
        [] => die "No holstate argument provided"
      | [x] => x
      | _ => die "Too many arguments"

val _ = PolyML.SaveState.loadState holstate
