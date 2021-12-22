val _ = use "../tools/Holmake/Systeml.sig";
val _ = use "Holmake/Systeml.sml";
val _ = use "poly/Binarymap.sig";
val _ = use "poly/Binarymap.sml";
val _ = use "poly/Binaryset.sig";
val _ = use "poly/Binaryset.sml";
val _ = use "poly/Listsort.sig";
val _ = use "poly/Listsort.sml";
val _ = use "../tools/Holmake/holpathdb.sig";
val _ = use "../tools/Holmake/holpathdb.sml";

open Systeml
structure Path = OS.Path
structure FileSys = OS.FileSys
structure Process = OS.Process
exception Interrupt = SML90.Interrupt;

val _ = use "../tools/Holmake/hmcore.ML";

fun warn s = (TextIO.output(TextIO.stdErr, s ^ "\n");
              TextIO.flushOut TextIO.stdErr)

fun main() = let
  val default = Systeml.DEFAULT_STATE
  val heap =
      if FileSys.access ("Holmakefile", [FileSys.A_READ]) then let
          open Holmake_types
          val holpathdb_extensions =
              holpathdb.search_for_extensions ReadHMF.find_includes
                {starter_dirs = [OS.FileSys.getDir()],
                 skip = holpathdb.db_dirs()}
          val _ = List.app holpathdb.extend_db holpathdb_extensions
          fun foldthis {vname,path} env = env_extend (vname, [LIT path]) env
          val env0 = holpathdb.fold foldthis (base_environment())
          val (env, _, _) = ReadHMF.read "Holmakefile" env0
          fun envlist id =
              map dequote (tokenize (perform_substitution env [VREF id]))
          val heap_v = envlist "HOLHEAP"
        in
          case heap_v of
            [] => default
          | [x] => x
          | _ => (warn "Malformed HOLHEAP definition in Holmakefile - \
                       \ignoring it";
                  default)
        end handle e => (warn "Bogus Holmakefile in current directory - \
                              \ignoring it]";
                         default)
      else default
  val heap = if Path.isRelative heap then Path.concat(FileSys.getDir(), heap)
             else heap
in
  TextIO.output(TextIO.stdOut, heap ^ "\n")
end
