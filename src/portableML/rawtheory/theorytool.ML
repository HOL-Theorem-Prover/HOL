datatype action = ShowKeys
                | ShowThyGraph
                | ShowUnused

datatype conf_record = CR of {
  action : action,
  help : bool,
  quiet : bool,
  url_base : string option,
  paths_from : string option
}

val init_conf =
  CR {action = ShowKeys, help = false, quiet = false, url_base = NONE,
      paths_from = NONE}

fun set_action a (CR {help, quiet, url_base, paths_from, ...}) =
  CR {action = a, help = help, quiet = quiet, url_base = url_base,
      paths_from = paths_from}

fun set_help () (CR {action, quiet, url_base, paths_from, ...}) =
  CR {action = action, help = true, quiet = quiet, url_base = url_base,
      paths_from = paths_from}

fun set_quiet () (CR {action, help, url_base, paths_from, ...}) =
  CR {action = action, help = help, quiet = true, url_base = url_base,
      paths_from = paths_from}

fun set_url_base s (CR {action, help, quiet, paths_from, ...}) =
  CR {action = action, help = help, quiet = quiet, url_base = SOME s,
      paths_from = paths_from}

fun set_paths_from s (CR {action, help, quiet, url_base, ...}) =
  CR {action = action, help = help, quiet = quiet, url_base = url_base,
      paths_from = SOME s}

val cline_options = [
  {short = "t", long = ["thygraph"],
   desc = GetOpt.NoArg (fn () => set_action ShowThyGraph),
   help = "Generate dep. graph for given theories (or all if list empty)"},
  {short = "u", long = ["unused"],
   desc = GetOpt.NoArg (fn () => set_action ShowUnused),
   help = "Scan and report unused theorems"},
  {short = "p", long = ["paths-from"],
   desc = GetOpt.ReqArg (set_paths_from, "file"),
   help = "Load only the *Theory.dat paths listed (one per line) in file, \
          \instead of scanning the file tree"},
  {short = "b", long = ["url-base"],
   desc = GetOpt.ReqArg (set_url_base, "dir"),
   help = "For --thygraph: emit per-node URLs as relative paths from dir \
          \to each theory's .hol/docs/<thy>Theory.html"},
  {short = "q", long = ["quiet"],
   desc = GetOpt.NoArg set_quiet,
   help = "Suppress file scanning output"},
  {short = "h", long = ["help"],
   desc = GetOpt.NoArg set_help,
   help = "Show this message"}
]

fun pp_dot_file thy_url (dom : string list, pairs : (string * string) list) =
    let
      open TextIO
      fun pr s = output(stdOut, s)
      fun pp_node s =
          case thy_url s of
              NONE => pr ("  " ^ s ^ "\n")
            | SOME u => pr ("  " ^ s ^ " [URL=\"" ^ u ^ "\"]\n")
    in
      pr "digraph G {\n";
      pr "  splines = ortho\n";
      pr "  bgcolor = transparent\n";
      pr "  ratio = compress\n";
      pr "  size = \"16,16\"\n";
      pr "  ranksep = 1.2\n";
      pr "  nodesep = 0.40\n";
      pr "  node [target=_parent shape=box3d margin=0.2 style=filled \
         \fillcolor=white fontcolor=darkgreen fontsize=30 fontname=Arial]\n";
      pr "  edge [arrowhead=dot]\n\n";
      List.app pp_node dom;
      pr "\n";
      List.app (fn (x,y) => pr ("  " ^ x ^ " -> " ^ y ^ "\n")) pairs;
      pr "}\n"
    end

(* Given an absolute base directory and an absolute target file, emit a
   relative URL.  Falls back to the bare filename if the relativization
   fails. *)
fun relativize {base, target} =
    OS.Path.mkRelative {path = target, relativeTo = base}
      handle OS.Path.Path =>
             #file (OS.Path.splitDirFile target)

fun absolutize p =
    if OS.Path.isAbsolute p then p
    else OS.Path.mkAbsolute {path = p, relativeTo = OS.FileSys.getDir()}

fun do_thygraph url_base files (g, links) =
    let
      open theorystats
      val parent_map = List.foldl (fn ((key, parents), acc) =>
          let val thy = #thy (#1 key)
              val ps = List.map #thy parents
          in Redblackmap.insert(acc, thy, ps) end)
          (Redblackmap.mkDict String.compare) links

      (* thy -> source directory (where its Script.sml / .hol/docs live) *)
      val dir_map = List.foldl (fn ((key, _), acc) =>
          let val thy = #thy (#1 key)
              val dir = #2 key
          in Redblackmap.insert(acc, thy, dir) end)
          (Redblackmap.mkDict String.compare) links

      val all_known_thys =
          Redblackmap.foldl (fn (k,_,acc) => k::acc) [] parent_map

      val target_thys = if null files then all_known_thys else files

      fun get_ancs [] visited edges = (visited, edges)
        | get_ancs (t::ts) visited edges =
            if Redblackset.member(visited, t) then
               get_ancs ts visited edges
            else
               let val visited' = Redblackset.add(visited, t)
                   val ps = Redblackmap.find(parent_map, t)
                            handle Redblackmap.NotFound => []
                   val edges' =
                       List.foldl (fn (p, acc) => (p, t) :: acc) edges ps
               in
                   get_ancs (ps @ ts) visited' edges'
               end

      val initial_visited = Redblackset.empty String.compare
      val (all_nodes_set, edges) = get_ancs target_thys initial_visited []
      val dom = Redblackset.listItems all_nodes_set

      val thy_url : string -> string option =
          case url_base of
              NONE => (fn s => SOME (s ^ "Theory.html"))
            | SOME base =>
              let
                val absbase = absolutize base
              in
                fn thy =>
                  case Redblackmap.peek(dir_map, thy) of
                      NONE => NONE
                    | SOME thydir =>
                      SOME (relativize {
                              base = absbase,
                              target = OS.Path.concat(
                                absolutize thydir,
                                ".hol/docs/" ^ thy ^ "Theory.html"
                              )
                            })
              end
    in
      pp_dot_file thy_url (dom, edges)
    end

fun warn s = (TextIO.output(TextIO.stdErr, s); TextIO.flushOut TextIO.stdErr)
fun warnln s = warn (s ^ "\n")

fun main() =
  let
    val uheader = "Usage: theorytool [options] [thyname1 thyname2 ...]"
    val uinfo = GetOpt.usageInfo {header = uheader, options = cline_options}
    val (cline_upds, files) =
        GetOpt.getOpt {argOrder = GetOpt.Permute,
                       options = cline_options,
                       errFn = fn s => theorystats.die (s ^ "\n" ^ uinfo)}
                      (CommandLine.arguments())
    val CR {action, help, quiet, url_base, paths_from} =
        List.foldl (fn (f, acc) => f acc) init_conf cline_upds
  in
    if help then (
        TextIO.output(TextIO.stdOut, uinfo);
        OS.Process.exit OS.Process.success
    ) else
    let
      val is_tty = terminal_primitives.strmIsTTY TextIO.stdErr
      val root = OS.FileSys.getDir()
      fun mkmsg p =
          let val base =
                  if String.isPrefix root p then
                    "." ^ String.extract(p, size root, NONE)
                  else p
          in
            StringCvt.padRight #" " 80 ("Scanning " ^ base)
          end

      val _ = theorystats.emit_scan_progress := (
        if quiet then (fn _ => ())
        else if is_tty then
          (fn s => warn ("\r" ^ mkmsg s ^ "\r"))
        else (fn s => warnln (mkmsg s ^ "\n"))
      )
      open theorystats

      fun read_path_lines fname =
          let
            val instrm = TextIO.openIn fname
            fun chomp s =
                if size s > 0 andalso String.sub(s, size s - 1) = #"\n"
                then String.substring(s, 0, size s - 1) else s
            fun loop acc =
                case TextIO.inputLine instrm of
                    NONE => List.rev acc
                  | SOME line =>
                    let val l = chomp line in
                      if l = "" then loop acc else loop (l :: acc)
                    end
          in
            loop [] before TextIO.closeIn instrm
          end handle e =>
                     die ("Failed to read paths file " ^ fname ^ ": " ^
                          General.exnMessage e)

      val (g, links) =
          case paths_from of
              SOME fname =>
              load_paths (read_path_lines fname) (TheoryGraph.empty, [])
            | NONE =>
              let
                val thy_file_map =
                  recurse_toDirs find_theory_files_action
                                 Symtab.empty
                                 [OS.FileSys.getDir()]
              in
                if not (null files) then
                  load_with_ancestors files thy_file_map
                                      (TheoryGraph.empty, [])
                else
                  recurse_toDirs find_theory_action
                                 (TheoryGraph.empty, [])
                                 [OS.FileSys.getDir()]
              end

      val _ = if not quiet andalso is_tty then
                (TextIO.output(
                  TextIO.stdOut,
                  StringCvt.padRight #" " 80 "\r" ^ "\r");
                 TextIO.flushOut TextIO.stdOut)
              else ()
    in
      case action of ShowKeys => (
          print "Keys:\n";
          List.app (println o HOLPP.pp_to_string 70
                    RawTheorykey.pp)
                   (TheoryGraph.keys g)
        )
      | ShowThyGraph => do_thygraph url_base files (g, links)
      | ShowUnused =>
        let
          val theories =
              List.map (fn key =>
                           let
                             val thy_name = #thy (#1 key)
                             val nd = TheoryGraph.get_node g key
                           in
                             (thy_name, nd)
                           end
                       ) (TheoryGraph.keys g)
          val _ = print ("Keys : " ^ String.concatWith ", " (map #1 theories) ^
                         "\n")
          fun foldthis (thyname, unused_names) () =
              print ("Unused in " ^ thyname ^ ":\n" ^
                     String.concat (map (fn s => "  " ^ s ^ "\n")
                                        (Redblackset.listItems unused_names)))
        in
          Symtab.fold foldthis (find_unused theories) ()
        end
    end
  end handle e =>
             theorystats.die ("Uncaught exception: " ^ General.exnMessage e)
