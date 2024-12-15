use "check_builds.sml";
open check_builds

fun handleArgs slist =
    let
      val d = OS.FileSys.getDir()
    in
      case slist of
          [] => [[d]]
        | ds => [map (fn s => OS.Path.mkAbsolute{path = s, relativeTo = d})
                     slist]
    end

fun main() =
    let val args = handleArgs (CommandLine.arguments())
        val problem_dirs0 = traverse args []
        val cpfx = commonPrefix problem_dirs0
        val n = size cpfx
        val problem_dirs = if cpfx = "/" orelse length problem_dirs0 = 1 then
                             problem_dirs0
                           else map (fn s => String.extract(s, n, NONE))
                                    problem_dirs0
    in
      List.app (fn s => if s = "" then print (" AND root = "^cpfx^"\n")
                        else print (s ^ "\n"))
               problem_dirs;
      OS.Process.exit OS.Process.success
    end
