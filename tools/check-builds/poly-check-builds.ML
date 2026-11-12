val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val origdir = OS.FileSys.getDir();
OS.FileSys.chDir "../../tools-poly";
val _ = use "poly/poly-init.ML";
OS.FileSys.chDir origdir;

structure BasicIO = SML90;
exception Interrupt = SML90.Interrupt

val _ = use "../../tools/Holmake/Systeml.sig"
val _ = use "../../tools/Holmake/Systeml.sml";
use "../../tools/Holmake/hmcore.ML";
use "check_builds.sml";
open check_builds

fun main() =
    let val (ignoring_file, args) = handleArgs (CommandLine.arguments())
        val ignores = case ignoring_file of NONE => [] | SOME f => readIgnores f
        val _ = configure_layout (case args of
                                      [d :: _] => d
                                    | _ => OS.FileSys.getDir())
        val problem_dirs0 = traverse ignores args []
        val cpfx = commonPrefix problem_dirs0
        val n = size cpfx
        val problem_dirs = if cpfx = "/" orelse length problem_dirs0 = 1 then
                             problem_dirs0
                           else map (fn s => String.extract(s, n, NONE))
                                    problem_dirs0
    in
      List.app (fn s => if s = "" then print (" AND root = "^cpfx^"\n")
                        else print (s ^ "\n"))
               (merge_sort problem_dirs);
      OS.Process.exit OS.Process.success
    end
