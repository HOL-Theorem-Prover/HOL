val _ = use "../tools/Holmake/Systeml.sig";
val _ = use "Holmake/Systeml.sml";
val _ = use "poly/Binarymap.sig";
val _ = use "poly/Binarymap.sml";
val _ = use "poly/Binaryset.sig";
val _ = use "poly/Binaryset.sml";
val _ = use "poly/Listsort.sig";
val _ = use "poly/Listsort.sml";

open Systeml
structure Path = OS.Path
structure FileSys = OS.FileSys
structure Process = OS.Process
val _ = let
  infix ++
  fun p1 ++ p2 = Path.concat (p1,p2)
  fun appthis s = let
    val nm = HOLDIR ++ "tools" ++ "Holmake" ++ s
  in
    use (nm ^ ".sig");
    use (nm ^ ".sml")
  end
in
  app appthis ["regexpMatch", "parse_glob", "internal_functions",
               "Holmake_types", "ReadHMF"]
end;

fun warn s = (TextIO.output(TextIO.stdErr, s ^ "\n");
              TextIO.flushOut TextIO.stdErr)

fun main() = let
  val default = Systeml.DEFAULT_STATE
  val heap =
      if FileSys.access ("Holmakefile", [FileSys.A_READ]) then let
          open Holmake_types
          val (env, _, _) = ReadHMF.read "Holmakefile" base_environment
          fun envlist id =
              map dequote (tokenize (perform_substitution env [VREF id]))
          val heap_v = envlist "HOLHEAP"
        in
          case heap_v of
            [] => default
          | [x] => x
          | _ => (warn "Malformed HOLHEAP definition in Holmakefile - ignoring it";
                  default)
        end handle e => (warn "Bogus Holmakefile in current directory - ignoring it]";
                         default)
      else default
  val heap = if Path.isRelative heap then Path.concat(FileSys.getDir(), heap)
             else heap
in
  TextIO.output(TextIO.stdOut, heap ^ "\n")
end
