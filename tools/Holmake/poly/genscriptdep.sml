structure genscriptdep :> sig val main : unit -> unit end =
struct

structure FileSys = OS.FileSys
structure Path = OS.Path
structure Process = OS.Process

infix ++
fun p1 ++ p2 = Path.concat(p1,p2)


fun warn s = (TextIO.output(TextIO.stdErr, s ^ "\n");
              TextIO.flushOut TextIO.stdErr)

fun get_includes () =
  if FileSys.access ("Holmakefile", [FileSys.A_READ]) then
    let
      open Holmake_types
      val (env, _, _) = ReadHMF.read "Holmakefile" (base_environment())
      fun envlist id =
        map dequote (tokenize (perform_substitution env [VREF id]))
    in
      envlist "PRE_INCLUDES" @ envlist "INCLUDES"
    end
    handle e => (warn "[bogus Holmakefile in current directory - ignoring it]";
                 [])
  else []

fun usage_str nm =
  "Usage:\n  " ^ nm ^ " [-h|-?|filename]\n"

fun usage ok =
  let
    val strm = if ok then TextIO.stdOut else TextIO.stdErr
  in
    TextIO.output(strm, usage_str (CommandLine.name()));
    Process.exit (if ok then Process.success else Process.failure)
  end

fun addPath I file =
  if OS.Path.isAbsolute file then
    file
  else let
      val p = List.find (fn p =>
                            FileSys.access (p ++ (file ^ ".ui"), []))
                        (FileSys.getDir() :: I)
    in
      case p of
           NONE => FileSys.getDir() ++ file
         | SOME p => p ++ file
    end;

fun main() =
  let
    open Holmake_tools
    val _ = holpathdb.extend_db {vname = "HOLDIR", path = Systeml.HOLDIR}
    val I = get_includes() @ [OS.Path.concat(Systeml.HOLDIR, "sigobj")]
  in
    case CommandLine.arguments() of
        ["-h"] => usage true
      | ["-?"] => usage true
      | [fname] =>
        let
          val {deps = deps0,...} =
              Holdep.main{assumes = [], includes = I,
                          diag = (fn s => ()), fname = fname}
          val deps = map toFile deps0
          fun mapthis (Unhandled _) = NONE
            | mapthis (DAT _) = NONE
            | mapthis f = SOME (fromFileNoSuf f)
          val depMods = List.map (addPath I) (List.mapPartial mapthis deps)
          fun usePathVars p = holpathdb.reverse_lookup {path = p}
          val depMods = List.map usePathVars depMods
        in
          List.app (fn s => print (s ^ "\n")) depMods
        end
      | _ => usage false
  end

end (* structure *)
