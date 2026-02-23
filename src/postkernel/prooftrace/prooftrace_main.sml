(* prooftrace: command-line tool for the HOL4 proof trace pipeline.

   Build, merge, and replay proof traces.

   Built as a standalone executable at bin/prooftrace.
*)

fun main () =
  let
    val args = CommandLine.arguments ()
    fun out s = TextIO.output(TextIO.stdOut, s)
    fun err s = TextIO.output(TextIO.stdErr, s)
    fun usage () = (
      out "Usage: prooftrace <command> [options] [args...]\n\
          \\n\
          \Commands:\n\
          \  build     Build theories with proof tracing enabled\n\
          \  merge     Merge per-theory traces for specified theorems\n\
          \  replay    Replay a trace, verify exports\n\
          \\n\
          \Build:\n\
          \  prooftrace build [holmake-args...]\n\
          \  prooftrace build --hol-build [build-args...]\n\
          \\n\
          \  Default: runs Holmake with HOL_TRACE_PROOFS=1, passing\n\
          \  through all arguments (targets, -j, etc.)\n\
          \  With --hol-build: runs bin/build instead.\n\
          \\n\
          \Merge:\n\
          \  prooftrace merge -o FILE [-d DIR]... THY.THM...\n\
          \\n\
          \  Finds .pftrace files in search directories (default: .),\n\
          \  merges traces needed for the given exports.\n\
          \  Exports are specified as theory.name pairs.\n\
          \\n\
          \Replay:\n\
          \  prooftrace replay [options] FILE\n\
          \\n\
          \  Replays from scratch in a minimal kernel session.\n\
          \  Reports pass/fail for each export.\n\
          \  --verbose       print each export's statement\n\
          \  --interactive   drop into REPL after replay with\n\
          \                  exports bound as ML values\n";
      OS.Process.exit OS.Process.success)
    fun die s = (
      err ("prooftrace: " ^ s ^ "\n");
      err "Try 'prooftrace --help' for usage.\n";
      OS.Process.exit OS.Process.failure)

    (* --- merge command --- *)
    fun do_merge args =
      let
        val output = ref (NONE : string option)
        val dirs = ref ([] : string list)
        val exports = ref ([] : (string * string) list)

        fun parse_export s =
          case String.fields (fn c => c = #".") s of
            [thy, name] => (thy, name)
          | _ => die ("bad export spec '" ^ s ^
                      "': expected THY.THM")

        fun parse [] = ()
          | parse ("--help" :: _) = usage ()
          | parse ("-h" :: _) = usage ()
          | parse ("-o" :: f :: rest) =
              (output := SOME f; parse rest)
          | parse ("-d" :: d :: rest) =
              (dirs := d :: !dirs; parse rest)
          | parse ("-o" :: []) = die "merge: -o requires an argument"
          | parse ("-d" :: []) = die "merge: -d requires an argument"
          | parse (arg :: rest) =
              if String.isPrefix "-" arg then
                die ("merge: unknown option: " ^ arg)
              else
                (exports := parse_export arg :: !exports;
                 parse rest)

        val _ = parse args
        val output_path = case !output of
            SOME p => p
          | NONE => die "merge: -o FILE is required"
        val desired = rev (!exports)
        val _ = if null desired then
                  die "merge: at least one THY.THM export is required"
                else ()
        val search_dirs = case !dirs of
            [] => ["."]
          | ds => rev ds

        (* Find all traces in search directories *)
        val all_traces = List.concat
          (map ReplayTrace.find_traces search_dirs)
        val _ = if null all_traces then
                  die "merge: no .pftrace files found"
                else
                  err ("Found " ^ Int.toString (length all_traces) ^
                       " trace files\n")
      in
        MergeTrace.merge {
          trace_paths = all_traces,
          desired_exports = desired,
          output_path = output_path
        }
      end

    (* --- dispatch --- *)
  in
    case args of
      [] => usage ()
    | ["--help"] => usage ()
    | ["-h"] => usage ()
    | ("build" :: _) => die "build: not yet implemented"
    | ("merge" :: rest) => do_merge rest
    | ("replay" :: _) => die "replay: not yet implemented"
    | (cmd :: _) => die ("unknown command: " ^ cmd)
  end
