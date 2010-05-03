structure mkmkcline =
struct

fun usage() =
    (TextIO.output(TextIO.stdErr,
                   "Usage: \n  " ^ CommandLine.name() ^
                   " [-o filename] [-static] [theory1 theory2 ...]\n");
     OS.Process.exit OS.Process.failure)


fun read_cline() =
    case CommandLine.arguments() of
      ["-o"] => usage()
    | "-static" :: rest => (NONE, rest, true)
    | "-o" :: file :: "-static" :: rest => (SOME file, rest, true)
    | "-o" :: file :: rest => (SOME file, rest, false)
    | x => (NONE, x, false)

end (* struct *)
