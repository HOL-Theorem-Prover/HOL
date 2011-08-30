(* this is an -*- sml -*- file *)
val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val _ = use "Holmake/Systeml.sig";
val _ = use "Holmake/Systeml.sml";
val _ = use "poly/Binarymap.sig";
val _ = use "poly/Binarymap.sml";
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
  app appthis ["internal_functions", "Holmake_types", "ReadHMF"]
end;

fun warn s = (TextIO.output(TextIO.stdErr, s ^ "\n");
              TextIO.flushOut TextIO.stdErr)

fun main() = let
  val default = Path.concat(HOLDIR, Path.concat("bin", "hol.builder"))
  val heap =
      if FileSys.access ("Holmakefile", [FileSys.A_READ]) then let
          open Holmake_types
          fun base_env s =
              case s of
                "HOLDIR" => [LIT HOLDIR]
              | "SIGOBJ" => [VREF "HOLDIR", LIT "/sigobj"]
              | _ => (case Process.getEnv s of
                        NONE => [LIT ""]
                      | SOME v => [LIT v])
          val toks = ReadHMF.read "Holmakefile"
          val env = extend_env toks base_env
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


val _ = PolyML.shareCommonData main
val _ = PolyML.export ("heapname", main);



