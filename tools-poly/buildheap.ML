val _ = PolyML.Compiler.prompt1 := "";
val _ = PolyML.Compiler.prompt2 := "";
val _ = PolyML.print_depth 0;


open TextIO
fun warn s = (output(stdErr, s ^ "\n"); flushOut stdErr)
fun die s = (warn s; OS.Process.exit OS.Process.failure)

fun fullPath ps = List.foldl (fn (p,acc) => OS.Path.concat(acc,p))
                             (hd ps) (tl ps);
use "../tools/Holmake/Systeml.sig";
use "Holmake/Systeml.sml";
open Systeml;

val defaultbase = Systeml.DEFAULT_STATE

fun usage() =
    (output(stdErr, "Usage:\n");
     output(stdErr, "  " ^ CommandLine.name() ^
                    " [-b baseheap] [-o outputheap] objs...\n\n");
     die ("Default output heap is a.out\n\
          \Default base heap is "^defaultbase))

fun update nm NONE newval = SOME newval
  | update nm (SOME _) _ =
    (warn ("Duplicate argument for "^nm); usage())

fun read_cline() = let
  val args = CommandLine.arguments()
  val _ = null args andalso usage()
  fun recurse args (objs, output, base) =
      case args of
        [] => (List.rev objs, output, base)
      | ["-o"] => usage()
      | ["-b"] => usage()
      | "-o"::oarg::rest =>
          recurse rest (objs, update "output heap" output oarg, base)
      | "-b"::barg::rest =>
          recurse rest (objs, output, update "base heap" base barg)
      | obj::rest => recurse rest (obj::objs, output, base)
in
  recurse args ([], NONE, NONE)
end

fun mkAbs p = OS.Path.mkAbsolute {relativeTo = OS.FileSys.getDir(), path = p}

fun create_heap (objs, outputheap0, base0) = let
  open Systeml
  val ofile = OS.FileSys.tmpName()
  val ostrm = openOut ofile
  fun p s = output(ostrm, s ^ "\n")
  fun system_ps s =
      if OS.Process.isSuccess (Systeml.system_ps s) then ()
      else die ("*** Failed to execute\n  "^s^"\nsuccessfully")
  val outputheap = mkAbs outputheap0
  val base = mkAbs base0
in
  p ("fun die s = (TextIO.output(TextIO.stdErr, s ^ \"\\n\"); \
     \OS.Process.exit OS.Process.failure)");
  p ("val _ = PolyML.SaveState.loadState \"" ^ String.toString base ^ "\"\n");
  p ("  handle e => die (General.exnMessage e)");
  p ("val heapname = \""^outputheap^"\";");
  p "local";
  p "fun hload s = (print (\"Loading \"^s^\"\\n\"); load s)";
  p "val _ = print \"\\n\";";
  p ("val _ = List.map hload [" ^
     String.concatWith "," (map (fn f => "\"" ^ String.toString f ^ "\"") objs) ^
     "] handle x => ((case x of Fail s => print (s^\"\\n\") | _ => ()); OS.Process.exit OS.Process.failure);");
  p "in";
  p ("val _ = PolyML.SaveState.saveChild(\""^ outputheap ^
     "\", List.length (PolyML.SaveState.showHierarchy()))");
  p ("val _ = print \"Exported "^outputheap^"\\n\"");
  p ("val _ = OS.Process.exit OS.Process.success");
  p ("end");
  closeOut ostrm;
  system_ps (Systeml.POLY ^ " -q < " ^ ofile)
end




fun main() = let
  val (objs, cloutput, clbase) = read_cline()
  val output = case cloutput of
                 NONE => "a.out"
               | SOME s => s
  val base = case clbase of
               NONE => defaultbase
             | SOME s => s
in
  create_heap (objs, output, base)
end
