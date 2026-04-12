datatype action = ShowKeys
                | ShowThyGraph
                | ShowUnused

datatype conf_record = CR of {
  action : action,
  help : bool,
  quiet : bool
}

val init_conf =
  CR {action = ShowKeys, help = false, quiet = false}

fun set_action a (CR {help, quiet, ...}) =
  CR {action = a, help = help, quiet = quiet}

fun set_help () (CR {action, quiet, ...}) =
  CR {action = action, help = true, quiet = quiet}

fun set_quiet () (CR {action, help, ...}) =
  CR {action = action, help = help, quiet = true}

val cline_options = [
  {short = "t", long = ["thygraph"],
   desc = GetOpt.NoArg (fn () => set_action ShowThyGraph),
   help = "Generate dep. graph for given theories (or all if list empty)"},
  {short = "u", long = ["unused"],
   desc = GetOpt.NoArg (fn () => set_action ShowUnused),
   help = "Scan and report unused theorems"},
  {short = "q", long = ["quiet"],
   desc = GetOpt.NoArg set_quiet,
   help = "Suppress file scanning output"},
  {short = "h", long = ["help"],
   desc = GetOpt.NoArg set_help,
   help = "Show this message"}
]

fun pp_dot_file (dom : string list, pairs : (string * string) list) =
    let
      open TextIO
      fun pr s = output(stdOut, s)
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
      List.app
        (fn s => pr ("  " ^ s ^ " [URL=\"" ^ s ^ "Theory.html\"]\n"))
        dom;
      pr "\n";
      List.app (fn (x,y) => pr ("  " ^ x ^ " -> " ^ y ^ "\n")) pairs;
      pr "}\n"
    end

fun do_thygraph files (g, links) =
    let
      open theorystats
      val parent_map = List.foldl (fn ((key, parents), acc) =>
          let val thy = #thy (#1 key)
              val ps = List.map #thy parents
          in Redblackmap.insert(acc, thy, ps) end)
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
    in
      pp_dot_file (dom, edges)
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
    val CR {action, help, quiet} =
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
      
      val thy_file_map =
        recurse_toDirs find_theory_files_action
                       (Symtab.empty)
                       [OS.FileSys.getDir()]
      
      val (g, links) =
        if action = ShowUnused andalso not (null files)
        then
          load_with_ancestors files thy_file_map
                              (TheoryGraph.empty, [])
        else
          recurse_toDirs find_theory_action
                         (TheoryGraph.empty, [])
                         [OS.FileSys.getDir()]
      
      val _ = if not quiet andalso is_tty then
                (TextIO.output(
                  TextIO.stdOut,
                  StringCvt.padRight #" " 80 "\r" ^ "\r");
                 TextIO.flushOut TextIO.stdOut)
              else ()
    in
      case action of
        ShowKeys => (
          print "Keys:\n";
          List.app (println o HOLPP.pp_to_string 70
                    RawTheorykey.pp)
                   (TheoryGraph.keys g)
        )
      | ShowThyGraph => do_thygraph files (g, links)
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
            val unused = find_unused theories
          in
            if null unused then
              println "No unused theorems found."
            else (
              println "Unused theorems:";
              List.app (fn (thm_ref, name) =>
                println (string_of_thm_ref thm_ref ^
                         ": " ^ name)
              ) unused
            )
          end
    end
  end handle e =>
             theorystats.die ("Uncaught exception: " ^ General.exnMessage e)
