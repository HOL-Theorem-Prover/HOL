structure main =
struct

open TextIO
fun usage () =
    (output(stdErr, "Usage: " ^ CommandLine.name() ^ " file.grm\n");
     OS.Process.exit OS.Process.failure)



fun main args =
    case args of
      [file] => ParseGen.parseGen file
    | _ => usage()

end
