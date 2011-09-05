val _ = PolyML.Compiler.prompt1 := "";
val _ = PolyML.Compiler.prompt2 := "";
val _ = PolyML.print_depth 0;


open TextIO
fun warn s = (output(stdErr, s ^ "\n"); flushOut stdErr)
fun die s = (warn s; OS.Process.exit OS.Process.failure)

fun fullPath ps = List.foldl (fn (p,acc) => OS.Path.concat(acc,p))
                             (hd ps) (tl ps);
use "Holmake/Systeml.sig";
use "Holmake/Systeml.sml";
open Systeml;

val defaultbase = fullPath [HOLDIR, "bin", "hol.builder"]

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

fun create_heap (objs, outputheap, base) = let
  open Systeml
  val ofile = OS.FileSys.tmpName()
  val ostrm = openOut ofile
  fun p s = output(ostrm, s ^ "\n")
in
  p ("val heapname = \""^outputheap^"\";");
  p "local";
  p "fun hload s = (print (\"Loading \"^s^\"\\n\"); load s)";
  p ("val _ = List.map hload [" ^
     String.concatWith "," (map (fn f => "\"" ^ String.toString f ^ "\"") objs) ^
     "] handle x => ((case x of Fail s => print (s^\"\\n\") | _ => ()); OS.Process.exit OS.Process.failure);");
  p "fun main() = (List.app use (CommandLine.arguments()); PolyML.rootFunction());";
  p "val _ = PolyML.shareCommonData main;";
  p "in";
  p ("val _ = PolyML.export(\""^ outputheap ^"\", main); end;");
  closeOut ostrm;
  system_ps (base ^ " < " ^ ofile);
  system_ps ("cc -o " ^ outputheap ^ " " ^ outputheap^".o" ^ " " ^
             String.concatWith " " POLY_LDFLAGS)
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
val _ = PolyML.shareCommonData main;
val _ = PolyML.export ("buildheap", ignore o main);
