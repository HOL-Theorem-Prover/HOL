structure BuildCommand :> BuildCommand =
struct

open Systeml Holmake_tools Holmake_types
structure FileSys = HOLFileSys
structure Path = OS.Path
structure Process = OS.Process

infix ++
fun p1 ++ p2 = Path.concat(p1,p2)
val SIGOBJ = Systeml.HOLDIR ++ "sigobj"



infix |>
fun x |> f = f x

val default_holstate = Systeml.DEFAULT_STATE

val _ = holpathdb.extend_db {vname = "HOLDIR", path = Systeml.HOLDIR}

open HM_GraphBuildJ1

datatype cmd_line = Mosml_compile of string list * string
                  | Mosml_link of string * string list
                  | Mosml_error

datatype buildresult = datatype multibuild.buildresult

fun process_mosml_args (outs:Holmake_tools.output_functions) c = let
  val {diag,...} = outs
  val diag = fn s => diag "mosml_args" (fn _ => s)
  fun isSource t = OS.Path.ext t = SOME "sig" orelse OS.Path.ext t = SOME "sml"
  fun isObj t = OS.Path.ext t = SOME "uo" orelse OS.Path.ext t = SOME "ui"
  val toks = String.tokens (fn c => c = #" ") c
  val c = ref false
  val q = ref false
  val obj = ref NONE
  val I = ref []
  val obj_files = ref ([] : string list)
  val src_file = ref NONE
  fun process_args [] = ()
    | process_args ("-c"::rest) = (c := true; process_args rest)
    | process_args ("-q"::rest) = process_args rest
    | process_args ("-toplevel"::rest) = process_args rest
    | process_args ("-o"::arg::rest) = (obj := SOME arg; process_args rest)
    | process_args ("-I"::arg::rest) = (I := arg::(!I); process_args rest)
    | process_args (file::rest) = let
      in
        if file = HM_BaseEnv.mosml_indicator then ()
        else if isSource file then
          src_file := SOME file
        else if isObj file then
          obj_files := file :: !obj_files
        else ();
        process_args rest
      end
in
  process_args toks;
  ((case (!c, !src_file, !obj_files, !obj) of
         (true, SOME f, ofs, NONE) => Mosml_compile (List.rev ofs, f)
       | (false, NONE, ofs, SOME f) => Mosml_link (f, List.rev ofs)
       | _ => let
           fun ostring NONE = "NONE"
             | ostring (SOME s) = "SOME "^s
         in
           diag ("mosml error: c = "^Bool.toString (!c)^", src_file = "^
                 ostring (!src_file) ^ ", obj = "^ostring (!obj));
           Mosml_error
         end),
   List.rev (!I))
end;




fun posix_diagnostic stat = let
  open Posix.Process
in
  case fromStatus stat of
    W_EXITSTATUS w8 => "exited with code "^Word8.toString w8
  | W_EXITED => "exited normally"
  | W_SIGNALED sg => "with signal " ^
                     SysWord.toString (Posix.Signal.toWord sg)
  | W_STOPPED sg => "stopped with signal " ^
                    SysWord.toString (Posix.Signal.toWord sg)
end

fun addPath incs (file : string) : dep =
    let
      val dir = FileSys.getDir()
      open hm_target
    in
      if OS.Path.dir file <> "" then filestr_to_tgt file
      else let
        val p = List.find (fn p =>
                              FileSys.access (p ++ (file ^ ".ui"), []))
                          (dir :: incs)
      in
        case p of
            NONE => mk(hmdir.curdir(), toFile file)
          | SOME p => mk(hmdir.fromPath {origin = dir, path = p}, toFile file)
      end
    end

fun time_max(t1,t2) = if Time.<(t1,t2) then t2 else t1

fun finish_compilation warn depMods0 filename tgt =
  case OS.Process.getEnv Systeml.build_after_reloc_envvar of
      NONE => OS.Process.success
    | SOME "1" =>
      let
        val filename_base = OS.Path.base filename
        val depMods = List.filter (fn s => s <> filename_base) depMods0
        fun getFTime fname =
          SOME (FileSys.modTime fname) handle OS.SysErr _ => NONE
        fun combine fname t =
          case getFTime fname of NONE => t | SOME t0 => time_max(t0,t)
        fun foldthis (modn, t) =
          t |> combine (modn ^ ".uo") |> combine (modn ^ ".ui")
        val startTime =
            case getFTime filename of
                NONE => (warn("Can't see base file " ^ filename ^
                              " though I just compiled it??");
                         Time.zeroTime)
              | SOME t => t
      in
        FileSys.setTime (tgt, SOME (List.foldl foldthis startTime depMods));
        OS.Process.success
      end
    | SOME s =>
      (warn ("Ignoring strange value (" ^ s ^ ") in " ^
             Systeml.build_after_reloc_envvar ^ " environment variable");
       OS.Process.success)

fun poly_compile warn diag quietp file I (deps : dep list) objs = let
  open hm_target
  val _ = diag (fn _ => "poly-compiling " ^ fromFile file ^ "\n  deps = [" ^
                        concatWithf tgt_toString ", " deps ^ "]\n  objs = [" ^
                        String.concatWith ", " objs ^ "]")
  val modName = fromFileNoSuf file
  val deps : hm_target.t list = let
    open Binaryset
    val dep_set0 = addList (empty_tgtset, deps)
    val {deps = extra_deps, ...} =
        Holdep.main {assumes = [], includes = I, diag = diag,
                     fname = fromFile file}
    val dep_set =
        addList (dep_set0, map filestr_to_tgt extra_deps)
  in
    listItems dep_set
  end
  val depfiles = map (toFile o tgt_toString) deps
  val _ = diag (fn _ =>
    "Depfiles are " ^
    String.concatWith ", " (map HOLFS_dtype.fileToString depfiles))
  val objfiles = map toFile objs
  fun mapthis (Unhandled _) = NONE
    | mapthis (DAT _) = NONE
    | mapthis f = SOME (fromFileNoSuf f)
  val depMods = List.mapPartial mapthis depfiles
  val objMods = List.map (addPath I) (List.mapPartial mapthis objfiles)
  fun usePathVars p = holpathdb.reverse_lookup {path = p}
  val depMods = List.map usePathVars (depMods @ map tgt_toString objMods)
  val say = if quietp then (fn s => ())
            else (fn s => FileSys.output(FileSys.stdOut, s ^ "\n"))
  val _ = say ("HOLMOSMLC -c " ^ fromFile file)
  val filename = tgt_toString (filestr_to_tgt (fromFile file))
  val _ = diag (fn _ => "Compiling " ^ HOLFS_dtype.fileToString file ^
                        "; writing target with dependencies: " ^
                        String.concatWith ", " depMods)
  fun uiOfCodeIsDep ct =
      let val file_ct = UI (HOLFileSys.map_CodeType OS.Path.file ct)
      in
        List.exists (fn tgt => filepart tgt = file_ct) deps
      end
in
case file of
  SIG _ =>
    (let
      val tgt = modName ^ ".ui"
      val outUi = FileSys.openOut tgt
     in
       FileSys.output (outUi, String.concatWith "\n" depMods);
       FileSys.output (outUi, "\n");
       FileSys.output (outUi, usePathVars filename ^ "\n");
       FileSys.closeOut outUi;
       finish_compilation warn depMods filename tgt
     end
     handle IO.Io _ => OS.Process.failure)
| SML ct =>
    (let
      val tgt = modName ^ ".uo"
      val outUo = FileSys.openOut tgt
     in
       FileSys.output (outUo, String.concatWith "\n" depMods);
       FileSys.output (outUo, "\n");
       FileSys.output (outUo, usePathVars filename ^ "\n");
       FileSys.closeOut outUo;
       if uiOfCodeIsDep ct then ()
       else
         let
           val _ = diag (fn _ => "Creating empty " ^ modName ^
                                 ".ui file as it is not a dependency")
           val outUi = FileSys.openOut (modName ^ ".ui")
         in
           FileSys.closeOut outUi;
           ignore (finish_compilation warn depMods filename (modName ^ ".ui"))
         end;
       finish_compilation warn depMods filename tgt
     end
     handle IO.Io _ => OS.Process.failure)
| _ => raise Match
end

fun list_delete x [] = []
  | list_delete x (y::ys) = if x = y then ys else y :: list_delete x ys

type 'a build_command = 'a HM_DepGraph.t ->
                        {preincludes : string list, includes : string list} ->
                        (dep,'a) Holmake_tools.buildcmds ->
                        File -> bool

fun make_build_command (buildinfo : HM_Cline.t buildinfo_t) = let
  val {optv,actual_overlay,envlist,quit_on_failure,outs,...} =
      buildinfo
  val hmenv = #hmenv buildinfo
  val {warn,diag,tgtfatal,...} = outs
  val keep_going = #keep_going (#core optv)
  val debug = #debug (#core optv)
  val opentheory = #opentheory (#core optv)
  val allfast = #fast (#core optv)
  val polynothol = #poly_not_hol optv
  val relocbuild = #relocbuild optv orelse
                   (case OS.Process.getEnv Systeml.build_after_reloc_envvar of
                        SOME "1" => true
                      | _ => false)
  val thmsrc = #thmsrc (#core optv)
  val interactive_flag = #interactive (#core optv)
  val quiet_flag = #quiet (#core optv)
  val cmdl_HOLSTATE = #holstate optv
  val jobs = #jobs (#core optv)
  val time_limit = #time_limit optv
  val maxheap = #maxheap optv
  val cache_dir = #cache_dir (#core optv)
  val chatty = if jobs = 1 then #chatty outs else (fn _ => ())
  val info = if jobs = 1 then #info outs else (fn _ => ())

  fun extra_poly_cline() = envlist "POLY_CLINE_OPTIONS"

  fun poly_link quietp extra result files =
  let
    open hm_target
    val _ = if not quietp then
              FileSys.output(FileSys.stdOut,
                             "HOLMOSMLC -o " ^ result ^ " " ^
                             String.concatWith " "
                                               (map (fn s => s ^ ".uo") files) ^
                             "\n")
            else ()
    val out = FileSys.openOut result
    fun p s =
        (FileSys.output (out, s); FileSys.output (out, "\n"))
  in
    p "#!/bin/sh";
    p ("set -e");
    (* Poly/ML runtime options (--gcthreads) must come before subcommand *)
    p (protect(fullPath [HOLDIR, "bin", "hol"]) ^ " --gcthreads=1 run " ^
       (case #holheap extra of NONE => "--poly"
                             | SOME d => "--holstate="^tgt_toString d) ^ " " ^
       (if isSome debug then "--dbg " else "") ^
       String.concatWith " " (extra_poly_cline()) ^ " " ^
       String.concatWith " " (map protect files));
    p ("exit 0");
    FileSys.closeOut out;
    Systeml.mk_xable result;
    OS.Process.success
  end handle IO.Io _ => OS.Process.failure

  fun build_command g (ii as {preincludes,includes}) c arg = let
    val diag = diag "build_command"
    val _ = diag (fn _ => "build_command on "^fromFile arg)
    val include_flags = preincludes @ includes
    val overlay_stringl = case actual_overlay of NONE => [] | SOME s => [s]
    exception CompileFailed
    exception FileNotFound
    val isSuccess = OS.Process.isSuccess
    fun setup_script s depinfo extras = let
      val scriptsml_file = SML (Script s)
      val scriptsml = fromFile scriptsml_file
      val script   = s^"Script"
      val scriptuo = script^".uo"
      val scriptui = script^".ui"
      (* first thing to do is to create the Script.uo file *)
      val b =
          case build_command g ii (Compile depinfo) scriptsml_file of
              BR_OK => true
            | BR_Failed => false
            | BR_ClineK _ => raise Fail "Compilation resulted in commandline"
      val _ = b orelse raise CompileFailed
      val _ = info ("Linking "^scriptuo^" to produce theory-builder executable")
      val objectfiles0 =
          if allfast then ["fastbuild.uo", scriptuo]
          else if quit_on_failure then [scriptuo]
          else ["holmakebuild.uo", scriptuo]
      val objectfiles0 = extras @ objectfiles0
      val objectfiles =
        if polynothol then
          objectfiles0
        else if interactive_flag then
          (SIGOBJ ++ "holmake_interactive.uo") :: objectfiles0
        else (SIGOBJ ++ "holmake_not_interactive.uo") :: objectfiles0
    in
        ((script,[scriptuo,scriptui,script]), objectfiles)
    end
    fun run_script cache_dir ck g (extra:GraphExtra.t) (script, intermediates) objectfiles
                   expecteds on_success =
      let
        fun safedelete s = FileSys.remove s handle OS.SysErr _ => ()
        (* The safedelete pass is defensive: with the build about to run
           and write fresh outputs, deleting any pre-existing copies first
           guards against a theory script that fails part-way through and
           leaves stale half-outputs lying around.  We could probably do
           without it.  But if we keep it, it must only fire on the
           cache-miss path: on a cache hit the expected files have just
           been put in place (possibly by a concurrent peer Holmake whose
           lock we inherited) and we must not delete them. *)
        fun prep_for_build () = app safedelete expecteds
        val useScript = fullPath [HOLDIR, "bin", "hol"]
        (* Poly/ML runtime options (--gcthreads, --maxheap) must come before subcommand *)
        val cline =
            useScript::"--gcthreads=1"::
            (case maxheap of
                 NONE => []
               | SOME n => ["--maxheap", Int.toString n]) @
            ["run"] @
            (case #multithread optv of
                 NONE => []
               | SOME i => ["--mt=" ^ Int.toString i]) @
            (case #holheap extra of NONE => "--poly"
                                  | SOME d => "--holstate="^tgt_toString d) ::
            extra_poly_cline() @
            ((if isSome debug then ["--dbg"] else []) @ objectfiles) @
            ["-e",
             "  check that export_theory call exists, and that new_theory\n\
             \  call is of the right name"] @
            List.concat (map (fn f => ["-c", f]) expecteds)
        fun cont wn res =
          let
            val _ =
                if not (isSuccess res) then
                  wn ("Failed script build for "^script^" - "^
                      posix_diagnostic res)
                else ()
            val _ = if isSuccess res orelse debug = NONE then
                      app safedelete (script :: intermediates)
                    else ()
            val _ = if isSuccess res then on_success () else ()
          in
            isSuccess res
          end
        val script_part =
            if String.isSuffix "Script" script then
              String.substring(script, 0, size script - 6)
            else raise Fail "Invariant failure in run_script"
        val other_nodes = let
          open HM_DepGraph
        in
          diag (fn _ => "Looking for other nodes with buildscript "^script);
          find_nodes_by_command g
              (hmdir.curdir(),
               BuiltInCmd (BIC_BuildScript script_part, empty_incinfo))
              (* incinfos not consulted for comparison so empty value ok here *)
        end
        (* Directories where parent Theory.dat files might live --
           every directory that has appeared as a target or dep in the
           graph.  HM_CacheFetch uses this to find current parents
           when validating cached .dat files; this lets downstream
           projects (with their own theory hierarchies outside core
           HOL's sigobj) benefit from the cache. *)
        val search_dirs = let
          open HM_DepGraph
          val ns = listNodes g
          fun add_dir (d, acc) =
              let val s = hmdir.toAbsPath d
              in if List.exists (fn x => x = s) acc then acc
                 else s :: acc
              end
          fun add_node ((_, nI), acc) =
              let val acc = add_dir (hm_target.dirpart (#target nI), acc)
              in
                List.foldl
                  (fn ((_,d),acc) => add_dir (hm_target.dirpart d, acc))
                  acc
                  (#dependencies nI)
              end
        in
          List.foldl add_node [] ns
        end
      in
          BR_ClineK { cline = (useScript, cline), job_kont = cont,
                      other_nodes = other_nodes,
                      cache_dir = cache_dir,
                      cachekey = ck,
                      search_dirs = search_dirs,
                      prep_for_build = prep_for_build }
      end
  in
    let
    in
      case (c : (dep,GraphExtra.t) buildcmds) of
          Compile (deps,_) =>
          let
            val file = fromFile arg
            val _ = exists_readable file orelse
                    (warn ("Wanted to compile "^file^
                            ", but it wasn't there\n");
                     raise FileNotFound)
            val res = poly_compile warn diag true arg include_flags deps []
          in
            if OS.Process.isSuccess res then BR_OK else BR_Failed
          end
        | BuildScript (s, deps, extra : GraphExtra.t) =>
          let
            val (scriptetc,objectfiles) = setup_script s (deps,extra) []
            (* When the script run succeeds, record the cachekey of its
               inputs to <thy>Theory.cachekey so that a subsequent
               Holmake invocation under --rebuild=cachekey can decide
               the target is up-to-date without re-running the script. *)
            val datFS =
                case HFS_NameMunge.HOLtoFS (s ^ "Theory.dat") of
                    SOME {fullfile, ...} => fullfile
                  | NONE => s ^ "Theory.dat"
            val stamp_path = HM_Cachekey.stamp_path_for_datfile datFS
            val _ = HM_Cachekey.remove_stamp stamp_path
            (* Discard the cache-updated graph: this code runs inside
               a forked child whose graph state isn't visible to
               anyone after the build completes. *)
            val ck = #1 (HM_Cachekey.compute_for_deps g deps)
            fun write_stamp () =
                case ck of
                    HM_Cachekey.Key k => HM_Cachekey.write_stamp stamp_path k
                  | HM_Cachekey.Missing _ => ()
            val cache_upload_dir = hmdir.toAbsPath (hmdir.curdir())
            val cache_filenames = let
              open HM_DepGraph
              val nodes = find_nodes_by_command g
                            (hmdir.curdir(),
                             BuiltInCmd (BIC_BuildScript s, empty_incinfo))
            in
              List.mapPartial
                (Option.map (fromFile o hm_target.filepart o #target) o
                 peeknode g)
                nodes
            end
            fun write_cache () =
                case cache_dir of
                    SOME url =>
                      ignore (HM_CacheFetch.upload url ck
                                cache_upload_dir
                                cache_filenames outs)
                  | NONE => ()
          in
            run_script cache_dir ck g extra scriptetc objectfiles
                       [s^"Theory.sml", s^"Theory.sig", s^"Theory.dat"]
                       (fn () => (write_stamp(); write_cache()))
          end
        | BuildArticle (s0, deps : dep list, extra) =>
          let
            open hm_target
            val s = s0 ^ ".art"
            val dep_set = Binaryset.addList(empty_tgtset, deps)
            val oldscript_str = s0 ^ "Script.sml"
            val fakescript_str = s ^ "Script.sml"
            val _ = Posix.FileSys.link {old = oldscript_str,
                                        new = fakescript_str }
            val loggingextras =
                case opentheory of SOME uo => [uo]
                                 | NONE => ["loggingHolKernel.uo"]
            val deps =
                (Binaryset.delete(dep_set, filestr_to_tgt oldscript_str)
                                 |> Binaryset.listItems) @
                [filestr_to_tgt fakescript_str]
            val ((script,inters),objectfiles) =
                setup_script s (deps,extra) loggingextras
          in
            run_script NONE (HM_Cachekey.Missing []) g extra
                       (script,fakescript_str :: inters) objectfiles
                       [s] (fn () => ())
          end
        | ProcessArticle (s,extra) =>
          let
            val raw_art_file = ART (RawArticle s)
            val art_file = ART (ProcessedArticle s)
            val raw_art = fromFile raw_art_file
            val art = fromFile art_file
            val cline =
                ("/bin/sh",
                 ["/bin/sh", "-c",
                  "opentheory info --article -o " ^ art ^ " " ^ raw_art])
          in
            BR_ClineK {cline = cline, job_kont = (fn _ => OS.Process.isSuccess),
                       other_nodes = [], cache_dir = NONE,
                       cachekey = HM_Cachekey.Missing [],
                       search_dirs = [],
                       prep_for_build = fn () => ()}
          end
    end handle CompileFailed => BR_Failed
             | FileNotFound  => BR_Failed
  end
  fun mosml_build_command hm_env extra {noecho, ignore_error, command = c} deps=
    let
      open Holmake_types
      val isHolmosmlcc =
          String.isPrefix (perform_substitution hm_env [VREF "HOLMOSMLC-C"]) c
      val isHolmosmlc =
          String.isPrefix (perform_substitution hm_env [VREF "HOLMOSMLC"]) c
      val isMosmlc =
          String.isPrefix (perform_substitution hm_env [VREF "MOSMLC"]) c
      val {diag,...} = outs
      val diag = diag "mosml_build"
    in
      if isHolmosmlcc orelse isHolmosmlc orelse isMosmlc then let
        val _ = diag (fn _ => "Processing mosml build command: "^c)
      in
        case process_mosml_args outs (if isHolmosmlcc then " -c " ^ c else c) of
            (Mosml_compile (objs, src), I) =>
            SOME (poly_compile warn diag (noecho orelse quiet_flag)
                               (toFile src)
                               I
                               deps
                               objs)
          | (Mosml_link (result, objs), I) =>
            let
            in
              diag (fn _ => "Moscow ML command is link -o "^result^" ["^
                            String.concatWith ", " objs ^ "]");
              SOME (poly_link (noecho orelse quiet_flag) extra result
                              (map OS.Path.base objs))
            end
          | (Mosml_error, _) =>
            (warn ("*** Couldn't interpret Moscow ML command: "^c);
             SOME (OS.Process.failure))
      end
      else NONE
    end
  val jobs = #jobs (#core optv)
  open HM_DepGraph
  fun pr s = s
  fun interpret_graph (g,ok) =
      (if ok then OS.Process.success else OS.Process.failure, g)
  fun interpret_bres bres =
    case bres of
        BR_OK => true
      | BR_ClineK{cline = (_,cl), job_kont = k, cache_dir, cachekey,
                  search_dirs, prep_for_build, ...} =>
        let val fetched = case cache_dir of
                              SOME url => HM_CacheFetch.fetch url cachekey
                                            search_dirs outs
                            | NONE => false
        in if fetched then true
           else (prep_for_build (); k warn (Systeml.systeml cl))
        end
      | BR_Failed => false


  fun system s =
    let val pfx = (if relocbuild then Systeml.build_after_reloc_envvar ^ "=1 "
                   else "") ^
                  (case thmsrc of SOME v => "HOL_THMSRC=" ^ v ^ " "
                                | NONE => "")
    in Systeml.system_ps (pfx ^ s)
    end

  val build_graph =
      if jobs = 1 then
        (fn g =>
            graphbuildj1 {
              build_command = (fn g => fn ii => fn cmds => fn f =>
                                  build_command g ii cmds f |> interpret_bres),
              mosml_build_command = mosml_build_command,
              outs = outs,
              keep_going = keep_going,
              quiet = quiet_flag,
              hmenv = hmenv,
              system = system } g)
      else
        (fn g =>
            multibuild.graphbuild { build_command = build_command,
                                    relocbuild = relocbuild,
                                    thmsrc = thmsrc,
                                    mosml_build_command = mosml_build_command,
                                    keep_going = keep_going,
                                    diag =
                                      (fn s => diag "multibuild" (fn _ => s)),
                                    time_limit = time_limit,
                                    maxheap = maxheap,
                                    quiet = quiet_flag, hmenv = hmenv,
                                    jobs = jobs,
                                    outs = outs } g |> interpret_graph)
in
  {extra_impl_deps = [],
   build_graph = build_graph}
end

end (* struct *)
