structure mkmkcline =
struct

fun usage() =
    (TextIO.output(TextIO.stdErr,
                   "Usage: \n  " ^ CommandLine.name() ^
                   " [-o filename] [theory1 theory2 ...]\n");
     OS.Process.exit OS.Process.failure)


fun read_cline() =
    case CommandLine.arguments() of
      ["-o"] => usage()
    | "-o" :: file :: rest => (SOME file, rest)
    | x => (NONE, x)

end (* struct *)
