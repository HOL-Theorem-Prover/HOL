(* prooftrace: command-line tool for the HOL4 proof trace pipeline.

   Build, merge, and replay proof traces.

   Built as a standalone executable at bin/prooftrace.
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
          \  prooftrace merge -o FILE [-d DIR]... THY.THM...\n\
          \\n\
          \  Finds .pft files in search directories (default: .),\n\
          \  merges traces needed for the given exports.\n\
          \  Exports are specified as theory.name pairs.\n\
          \\n\
          \Replay:\n\
          \  prooftrace replay [options] FILE\n\
          \\n\
          \  Replays a trace from scratch in a minimal kernel session.\n\
          \  Reports pass/fail for each export. Exits with success if\n\
          \  all exports are oracle-free, failure otherwise.\n\
          \\n\
          \  --verbose       print each export's statement\n\
          \  --interactive   drop into HOL REPL after replay with\n\
          \                  exports bound as prooftrace_exports\n\
          \  --load LIB      load additional library after replay\n\
          \                  (repeatable; for extra pretty printing)\n\
          \  --load-hol      load standard HOL libraries after replay\n\
          \                  (boolLib etc.) for standard pretty printing\n\
          \\n\
          \Examples:\n\
          \  prooftrace replay merged.pft\n\
          \  prooftrace replay --verbose --load-hol merged.pft\n\
          \  prooftrace replay --interactive --load-hol merged.pft\n";
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

        val all_traces = List.concat
          (map ReplayTrace.find_traces search_dirs)
        val _ = if null all_traces then
                  die "merge: no .pft files found"
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

    (* --- replay command --- *)
    fun do_replay args =
      let
        val verbose = ref false
        val interactive = ref false
        val load_hol = ref false
        val loads = ref ([] : string list)
        val file = ref (NONE : string option)

        fun parse [] = ()
          | parse ("--help" :: _) = usage ()
          | parse ("-h" :: _) = usage ()
          | parse ("--verbose" :: rest) =
              (verbose := true; parse rest)
          | parse ("--interactive" :: rest) =
              (interactive := true; parse rest)
          | parse ("--load-hol" :: rest) =
              (load_hol := true; parse rest)
          | parse ("--load" :: lib :: rest) =
              (loads := lib :: !loads; parse rest)
          | parse ("--load" :: []) =
              die "replay: --load requires an argument"
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
        (* Replay always via bin/hol --min for a fresh kernel *)
        let
          val script = OS.FileSys.tmpName ()
          val s = TextIO.openOut script
          fun wr x = TextIO.output(s, x)
          val hol_libs = if !load_hol then ["bossLib", "holTheory"] else []
          val all_loads = hol_libs @ rev (!loads)
          val load_lines = map (fn lib =>
            "val _ = Meta.load \"" ^ String.toString lib ^ "\";")
            all_loads
          val verbose_lines = if !verbose then [
            "val _ = List.app (fn (name, th) =>",
            "  let val concl = (Parse.term_to_string (Thm.concl th)",
            "                   handle _ => \"<unprintable>\")",
            "      val hyps = Thm.hyp th",
            "      val hyp_str = if null hyps then \"\"",
            "        else \" [\" ^ Int.toString (length hyps) ^ \" hyps]\"",
            "      val tags = #1 (Tag.dest_tag (Thm.tag th))",
            "      val status = if null tags then \"OK\"",
            "        else \"ORACLE[\" ^ String.concatWith \",\" tags ^ \"]\"",
            "  in print (status ^ \" \" ^ name ^ \": \" ^ concl",
            "            ^ hyp_str ^ \"\\n\") end)",
            "  prooftrace_exports;"
          ] else []
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
          val lines =
            ["load \"ReplayTrace\";",
             "load \"Parse\";",
             "val prooftrace_exports = ReplayTrace.replay_file",
             "  \"" ^ String.toString abs_path ^ "\";"] @
            load_lines @
            ["val _ = List.app (fn (name, th) =>",
             "  let val tags = #1 (Tag.dest_tag (Thm.tag th))",
             "      val status = if null tags then \"OK\" else \"ORACLE\"",
             "  in print (status ^ \" \" ^ name ^ \"\\n\") end)",
             "  prooftrace_exports;"] @
            verbose_lines @
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
    case args of
      [] => usage ()
    | ["--help"] => usage ()
    | ["-h"] => usage ()
    | ("merge" :: rest) => do_merge rest
    | ("replay" :: rest) => do_replay rest
    | (cmd :: _) => die ("unknown command: " ^ cmd)
  end
