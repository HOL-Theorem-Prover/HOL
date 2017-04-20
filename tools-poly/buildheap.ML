val _ = PolyML.Compiler.prompt1 := "";
val _ = PolyML.Compiler.prompt2 := "";
val _ = PolyML.print_depth 0;

local
open TextIO
in
fun warn s = (output(stdErr, s ^ "\n"); flushOut stdErr)
fun die (s:string) : 'a = (warn s; OS.Process.exit OS.Process.failure)
end

fun member s [] = false
  | member s (h::t) = s = h orelse member s t

fun fullPath ps = List.foldl (fn (p,acc) => OS.Path.concat(acc,p))
                             (hd ps) (tl ps);
use "../tools/Holmake/Systeml.sig";
use "Holmake/Systeml.sml";
open Systeml;

val defaultbase = Systeml.DEFAULT_STATE

fun usage() =
    (warn "Usage:";
     warn ("  " ^ CommandLine.name() ^
           " [-F] [-q] [-b baseheap] [-o outputheap] ([-f] obj)* ...\n");
     die ("  -F to make all objects forced (use with care!)\n\
          \  -f before an object to force inclusion even though path looks \
          \odd\n\
          \  -q for minimal output (quiet mode)\n\
          \\n\
          \  Default output heap is a.out\n\
          \  Default base heap is "^defaultbase))

fun update nm NONE newval = SOME newval
  | update nm (SOME _) _ =
    (warn ("Duplicate argument for "^nm); usage())

fun read_cline() = let
  val args = CommandLine.arguments()
  val _ = null args andalso usage()
  fun recurse args (objs, output, base, seenF, quietp) =
      case args of
        [] => (List.rev objs, output, base, quietp)
      | ["-o"] => usage()
      | ["-b"] => usage()
      | ["-f"] => usage()
      | "-F"::rest => recurse rest (objs, output, base, true, quietp)
      | "-q" :: rest => recurse rest (objs, output, base, seenF, true)
      | "-o"::oarg::rest =>
          recurse rest
                  (objs, update "output heap" output oarg, base, seenF, quietp)
      | "-b"::barg::rest =>
          recurse rest
                  (objs, output, update "base heap" base barg, seenF, quietp)
      | "-f"::obj::rest =>
          recurse rest ((obj,true)::objs, output, base, seenF, quietp)
      | obj::rest =>
          recurse rest ((obj,seenF)::objs, output, base, seenF, quietp)
in
  recurse args ([], NONE, NONE, false, false)
end

fun mkAbs p = OS.Path.mkAbsolute {relativeTo = OS.FileSys.getDir(), path = p}

infix ++
val op ++ = OS.Path.concat
fun hol_use p s =
  let
    val nm = HOLDIR ++ p ++ s
  in
    use (nm ^ ".sig")
  ; use (nm ^ ".sml")
  end;

exception Interrupt = SML90.Interrupt;

List.app (hol_use ("tools-poly" ++ "poly"))
         ["Binaryset", "Binarymap", "Listsort"];
List.app (hol_use ("tools" ++ "Holmake"))
         ["regexpMatch", "parse_glob", "internal_functions",
          "Holdep_tokens", "Holdep", "Holmake_tools", "Holmake_types",
          "ReadHMF"];

fun findUo [] _ = NONE
  | findUo (search::rest) modPath =
      let val path =
         OS.Path.mkAbsolute
           {path = modPath, relativeTo = OS.Path.mkAbsolute
                                           {path=search,
                                            relativeTo = OS.FileSys.getDir ()}};
      in
        if OS.FileSys.access (path, []) then
          SOME path
        else
          findUo rest modPath
      end;

fun check_objpath die incs (p, b) =
  if b then ()
  else
    if member (OS.Path.dir p) incs then ()
    else die ("Object file "^p^" has suspicious path; use -f to override")

fun time_max (t1, t2) = if Time.<(t1,t2) then t2 else t1

fun create_heap qp findMod (objs, outputheap0, base0) = let
  open Systeml TextIO
  val ofile = OS.FileSys.tmpName()
  val ostrm = openOut ofile
  fun p s = output(ostrm, s ^ "\n")
  val original_die = die
  fun die s =
      if qp then OS.Process.exit OS.Process.failure
      else original_die s
  val (diestr,hloadstr,printstr) =
      if qp then
        ("fun die s = OS.Process.exit OS.Process.failure;",
         "fun hload s = load s;",
         "fun print s = ();")
      else
        ("fun die s = (TextIO.output(TextIO.stdErr, s ^ \"\\n\"); \
         \OS.Process.exit OS.Process.failure)",
         "fun hload s = (print (\"Loading \"^s^\"\\n\"); load s);",
         "\n")
  fun system_ps s =
      if OS.Process.isSuccess (Systeml.system_ps s) then ()
      else die ("*** Failed to execute\n  "^s^"\nsuccessfully")
  val outputheap = mkAbs outputheap0
  val base = mkAbs base0
in
  p diestr;
  p ("val _ = PolyML.SaveState.loadState \"" ^ String.toString base ^ "\"\n");
  p ("  handle e => die (General.exnMessage e)");
  p ("val heapname = \""^outputheap^"\";");
  p ("val _ = List.app holpathdb.extend_db\n");
  p ("(holpathdb.search_for_extensions ReadHMF.find_includes\n");
  p ("[OS.FileSys.getDir()]);\n");
  p "local";
  p hloadstr;
  p printstr;
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
  system_ps (Systeml.POLY ^ " -q < " ^ ofile);
  case OS.Process.getEnv Systeml.build_after_reloc_envvar of
      NONE => ()
    | SOME "1" =>
      let
        val getTime = OS.FileSys.modTime o findMod
        fun foldthis (modname, t0) = time_max(t0, getTime modname)
      in
        OS.FileSys.setTime (outputheap,
                            SOME (foldl foldthis (getTime (hd objs)) (tl objs)))
      end
    | SOME s =>
      warn ("Ignoring strange value (" ^ s ^ ") for " ^
            Systeml.build_after_reloc_envvar)
end




fun main() = let
  val (objs0, cloutput, clbase, qp) = read_cline()
  val warn = if qp then (fn s => ()) else warn
  val original_die = die
  fun die s = if qp then OS.Process.exit OS.Process.failure else original_die s
  val allincs =
      if OS.FileSys.access ("Holmakefile", [OS.FileSys.A_READ]) then let
        open Holmake_types
        val (env, _, _) = ReadHMF.read "Holmakefile" (base_environment())
        fun envlist id =
          map dequote (tokenize (perform_substitution env [VREF id]))
      in
        envlist "INCLUDES" @ envlist "PRE_INCLUDES"
      end handle e =>
                 (warn "[bogus Holmakefile in current directory - ignoring it]";
                  [])
      else []
  val _ = List.app (check_objpath die ("" :: "." :: allincs)) objs0
  val output = case cloutput of
                   NONE => "a.out"
                 | SOME s => s
  val base = case clbase of
               NONE => defaultbase
             | SOME s => s
  val search_these = "." :: OS.Path.concat(Systeml.HOLDIR, "sigobj") :: allincs
  fun findmod s =
    case findUo search_these (s ^ ".uo") of
        NONE => die ("In "^OS.FileSys.getDir()^": couldn't find "^s^".uo\n\
                     \After searching: " ^ String.concatWith ", " search_these)
      | SOME p => p
in
  create_heap qp findmod (map #1 objs0, output, base)
end
