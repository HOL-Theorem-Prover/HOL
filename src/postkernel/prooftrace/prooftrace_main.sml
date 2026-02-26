(* prooftrace: command-line tool for the HOL4 proof trace pipeline.

   Build, merge, and replay proof traces.

   Built as a standalone executable at bin/prooftrace, using only
   kernel dependencies (no bossLib or pretty-printing libraries).

   Replay launches bin/hol --min as a subprocess for a fresh
   kernel session. In default (verbose) mode, Parse is loaded in
   the subprocess for basic term printing. Pretty-printing via
   full HOL libraries is planned for a future version.
*)

fun main () =
  let
    val args = CommandLine.arguments ()
    val holdir = Systeml.HOLDIR
    fun out s = TextIO.output(TextIO.stdOut, s)
    fun err s = TextIO.output(TextIO.stdErr, s)
    fun usage () = (
      out "Usage: prooftrace <command> [options] [args...]\n\
          \\n\
          \Commands:\n\
          \  merge     Merge per-theory traces for specified theorems\n\
          \  replay    Replay a trace, verify exports\n\
          \\n\
          \Building with traces:\n\
          \  bin/build --trace                   (HOL sources)\n\
          \  Holmake --trace                     (external projects)\n\
          \\n\
          \Merge:\n\
          \  prooftrace merge [-q] -o FILE [-d DIR]... THY.THM...\n\
          \\n\
          \  Recursively finds .pft files in search directories\n\
          \  (. is always included), merges traces needed for the\n\
          \  given exports. Exports are specified as theory.name pairs.\n\
          \\n\
          \Replay:\n\
          \  prooftrace replay [options] FILE\n\
          \\n\
          \  Replays a trace from scratch in a minimal kernel session.\n\
          \  Prints each export with its statement and verification\n\
          \  status. Exits with success if all exports are oracle-free.\n\
          \\n\
          \  --concise       print only export names, not statements\n\
          \  --interactive   drop into HOL REPL after replay with\n\
          \                  exports bound as prooftrace_exports\n\
          \\n\
          \Examples:\n\
          \  prooftrace replay merged.pft\n\
          \  prooftrace replay --concise merged.pft\n\
          \  prooftrace replay --interactive merged.pft\n";
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
        val quiet = ref false

        fun parse_export s =
          case String.fields (fn c => c = #".") s of
            [thy, name] => (thy, name)
          | _ => die ("bad export spec '" ^ s ^
                      "': expected THY.THM")

        fun parse [] = ()
          | parse ("--help" :: _) = usage ()
          | parse ("-h" :: _) = usage ()
          | parse ("-q" :: rest) =
              (quiet := true; parse rest)
          | parse ("--quiet" :: rest) =
              (quiet := true; parse rest)
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
        val search_dirs =
          let val ds = rev (!dirs)
          in if List.exists (fn d => d = ".") ds then ds
             else "." :: ds
          end

        val all_traces = List.concat
          (map ReplayTrace.find_traces search_dirs)
        val _ = if null all_traces then
                  die "merge: no .pft files found"
                else if not (!quiet) then
                  err ("Found " ^ Int.toString (length all_traces) ^
                       " trace files\n")
                else ()
      in
        MergeTrace.merge {
          trace_paths = all_traces,
          desired_exports = desired,
          output_path = output_path,
          quiet = !quiet
        }
      end

    (* --- replay command --- *)
    fun do_replay args =
      let
        val concise = ref false
        val interactive = ref false
        val file = ref (NONE : string option)

        fun parse [] = ()
          | parse ("--help" :: _) = usage ()
          | parse ("-h" :: _) = usage ()
          | parse ("--concise" :: rest) =
              (concise := true; parse rest)
          | parse ("--interactive" :: rest) =
              (interactive := true; parse rest)
          | parse (arg :: rest) =
              if String.isPrefix "-" arg then
                die ("replay: unknown option: " ^ arg)
              else
                (case !file of
                   NONE => file := SOME arg
                 | SOME _ => die "replay: only one trace file allowed";
                 parse rest)

        val _ = parse args
        val path = case !file of
            SOME p => p
          | NONE => die "replay: trace file argument is required"

        val abs_path = OS.Path.mkAbsolute
          {path = path, relativeTo = OS.FileSys.getDir ()}
      in
        (* Replay via bin/hol --min for a fresh kernel *)
        let
          val script = OS.FileSys.tmpName () ^ ".sml"
          val s = TextIO.openOut script
          fun wr x = TextIO.output(s, x)

          (* Print each export: name, status, and optionally statement.
             In default (non-concise) mode, load Parse for basic term
             printing (no full HOL libraries, just the parser/printer). *)
          val print_lines = if !concise then [
            "val _ = List.app (fn (name, th) =>",
            "  let val tags = #1 (Tag.dest_tag (Thm.tag th))",
            "      val status = if null tags then \"OK\" else \"ORACLE\"",
            "  in print (status ^ \" \" ^ name ^ \"\\n\") end)",
            "  prooftrace_exports;"
          ] else [
            "val _ = (load \"Parse\" handle _ => ());",
            "val _ = List.app (fn (name, th) =>",
            "  let val concl = Parse.term_to_string (Thm.concl th)",
            "                   handle _ => \"<unprintable>\"",
            "      val hyps = Thm.hyp th",
            "      val hyp_str = if null hyps then \"\"",
            "        else \" [\" ^ Int.toString (length hyps) ^ \" hyps]\"",
            "      val tags = #1 (Tag.dest_tag (Thm.tag th))",
            "      val status = if null tags then \"OK\"",
            "        else \"ORACLE[\" ^ String.concatWith \",\" tags ^ \"]\"",
            "  in print (status ^ \" \" ^ name ^ \": \" ^ concl",
            "            ^ hyp_str ^ \"\\n\") end)",
            "  prooftrace_exports;"
          ]

          val summary_lines = [
            "val _ = let",
            "  val n = length prooftrace_exports",
            "  val n_oracle = length (List.filter (fn (_,th) =>",
            "    not (null (#1 (Tag.dest_tag (Thm.tag th)))))",
            "    prooftrace_exports)",
            "in print (\"\\n\" ^ Int.toString (n - n_oracle) ^ \"/\"",
            "  ^ Int.toString n ^ \" exports verified clean\"",
            "  ^ (if n_oracle > 0 then \" (\" ^ Int.toString n_oracle",
            "     ^ \" with oracle tags)\" else \"\") ^ \"\\n\") end;"
          ]

          val exit_lines = if !interactive then [
            "val _ = print \"\\nExports bound as prooftrace_exports.\\n\";"
          ] else [
            "val _ = OS.Process.exit (if List.all (fn (_,th) =>",
            "  null (#1 (Tag.dest_tag (Thm.tag th))))",
            "  prooftrace_exports",
            "  then OS.Process.success else OS.Process.failure);"
          ]

          val replay_lines =
            [(* Deactivate proof tracing in the replay subprocess
                so it doesn't record a trace of the replay itself *)
             "val _ = (Thm.trace_hook := NONE;",
             "         Thm.trace_export_hook := NONE);",
             "load \"ReplayTrace\";",
             "val {exports = prooftrace_exports,",
             "     replay_maps = prooftrace_replay_maps} =",
             "  ReplayTrace.replay_file",
             "  \"" ^ String.toString abs_path ^ "\";"]

          val interactive_load_lines = if !interactive then [
            "(* Set replay map, then load theories *)",
            "val _ = Thm.replay_thms :=",
            "  SOME prooftrace_replay_maps;",
            "val prooftrace_theories =",
            "  Redblackset.listItems",
            "    (Redblackmap.foldl (fn ((thy,_),_,s) =>",
            "       Redblackset.add(s,thy))",
            "     (Redblackset.empty String.compare)",
            "     (#named prooftrace_replay_maps));",
            "val _ = (List.app (fn thy =>",
            "           load (thy ^ \"Theory\")",
            "           handle e => print (\"WARNING: failed to load \"",
            "             ^ thy ^ \": \" ^ General.exnMessage e ^ \"\\n\"))",
            "         prooftrace_theories",
            "         handle e => (Thm.replay_thms := NONE; raise e));",
            "(* Load bossLib (and its deps) with replay_thms still set,",
            "   so all theory loading gets replay substitution. *)",
            "val _ = (load \"bossLib\"",
            "         handle e => (Thm.replay_thms := NONE; raise e));",
            "val _ = Thm.replay_thms := NONE;",
            "(* Run preludes for pretty-printers and interactive setup.",
            "   hol.state.min is built with buildheap --poly which",
            "   skips the normal preludes; we run them now.",
            "   This matches load_preludes() in hol.ML. *)",
            "val _ = List.app load",
            "  [\"Arbint\", \"Arbrat\", \"Inttab\", \"KNametab\"];",
            "val _ = QUse.use (OS.Path.concat(Systeml.HOLDIR,",
            "          \"tools-poly/prelude.ML\"));",
            "val _ = QUse.use (OS.Path.concat(Systeml.HOLDIR,",
            "          \"tools-poly/prelude2.ML\"));"
          ] else []

          val lines =
            replay_lines @
            interactive_load_lines @
            print_lines @
            summary_lines @
            exit_lines
          val _ = List.app (fn l => wr (l ^ "\n")) lines
          val _ = TextIO.closeOut s
          val hol = OS.Path.concat(holdir, "bin/hol")
          val cmdline = hol ^ " --min " ^ script
        in
          err ("Replaying: " ^ abs_path ^ "\n");
          OS.Process.exit (OS.Process.system cmdline)
        end
      end

    (* --- dispatch --- *)
  in
    (case args of
      [] => usage ()
    | ["--help"] => usage ()
    | ["-h"] => usage ()
    | ("merge" :: rest) => do_merge rest
    | ("replay" :: rest) => do_replay rest
    | (cmd :: _) => die ("unknown command: " ^ cmd))
    handle e =>
      (err ("prooftrace: unhandled exception: " ^
            General.exnMessage e ^ "\n");
       OS.Process.exit OS.Process.failure)
  end
