(*---------------------------------------------------------------------------
     A special purpose version of make that "does the right thing" in
     single directories for building HOL theories, and accompanying
     SML libraries.
 ---------------------------------------------------------------------------*)

structure Holmake =
struct

open Systeml Holmake_tools Holmake_types HOLFileSys
infix forces_update_of depforces_update_of |>

structure FileSys = HOLFileSys
structure Path = OS.Path
structure Process = OS.Process

fun slist_to_set slist =
    Binaryset.addList(Binaryset.empty String.compare, slist)
fun flist_to_set flist =
    Binaryset.addList(Binaryset.empty file_compare, flist)
fun slist_to_dset basedir slist =
    List.foldl
      (fn (s,dset) =>
          Binaryset.add(dset, hmdir.extendp {base=basedir, extension=s}))
      (Binaryset.empty hmdir.compare) slist
fun deplist_to_set ds = Binaryset.addList(hm_target.empty_tgtset, ds)
val filestr_to_tgt = hm_target.filestr_to_tgt
val envlist = Holmake_types.envlist

fun chattiness_level (switches : HM_Core_Cline.t) =
  case (#debug switches, #verbose switches, #quiet switches) of
      (SOME _, _, _) => 3
    | (_, true, _) => 2
    | (_, _, true) => 0
    | _ => 1

fun main() = let

val execname = Path.file (CommandLine.name())
fun warn s = stdErr_out (execname^": "^s^"\n")
fun die s = (warn s; Process.exit Process.failure)
(* like die, but without the "Holmake:" prefix: $(error ...) and other
   GNU-make-style abort messages already carry their own "file:line:"
   prefix and shouldn't be re-tagged. *)
fun die_raw s = (stdErr_out (s ^ "\n"); Process.exit Process.failure)

fun is_src_dir hmd =
    let val s = nice_dir (hmdir.pretty_dir hmd)
    in
      String.isPrefix "$(HOLDIR)/src/" s
    end
fun in_src () = is_src_dir (hmdir.curdir())

(* Global parameters, which get set at configuration time *)
val HOLDIR0 = Systeml.HOLDIR;
val DEPDIR = Systeml.DEPDIR
val LOGDIR = Systeml.LOGDIR

local
  val sigobj = OS.Path.concat(HOLDIR0, "sigobj")
  val frakS = String.implode (map Char.chr [0xF0,0x9D,0x94,0x96])
in
fun ppath s = if String.isPrefix sigobj s then
                frakS ^ String.extract(s,size sigobj,NONE)
              else s

fun pflist fs = concatWithf (ppath o fromFile) ", " fs
fun pdlist ds = concatWithf tgt_toString ", " ds
end


(** Command line parsing *)

(*** parse command line *)
fun apply_updates fs v = List.foldl (fn (f,v) => #update f (warn,v)) v fs

fun getcline args =
  let
    open GetOpt
    val (opts, rest) = getOpt {argOrder = Permute,
                               options = HM_Cline.option_descriptions,
                               errFn = die}
                              args
    fun is_varassign str =
      let
        val fs = String.fields (fn x => x = #"=") str
      in
        List.length fs = 2 andalso List.all (fn s => String.size s > 0) fs
      end
    val (vars, targets) = List.partition is_varassign rest
  in
    (opts, vars, targets)
  end

(* Run the lastmaker / "am I in the right HOLDIR?" checks BEFORE
   the full cline parse and any chdir.  We peek at -C/--directory
   and --nolmbc directly out of argv so do_lastmade_checks can
   target the user's intended working directory (where its
   .HOLMK/lastmaker file lives), but the running process stays in
   its original cwd.  If lastmaker exec-switches to a different
   Holmake binary, the spawned shell inherits the original cwd and
   the child's own cline parse handles -C the normal way (one
   chdir, via set_cwd).  If we don't exec-switch, control falls
   through to the regular getcline/apply_updates flow below, which
   sees the same argv and chdirs at its usual point. *)
local
  val rawargs = CommandLine.arguments()
  fun peek_chdir [] = NONE
    | peek_chdir ("-C" :: d :: _) = SOME d
    | peek_chdir ("--directory" :: d :: _) = SOME d
    | peek_chdir (a :: rest) =
        if String.isPrefix "--directory=" a then
          SOME (String.extract (a, size "--directory=", NONE))
        else peek_chdir rest
in
val _ = do_lastmade_checks default_ofns
          {no_lastmakercheck =
             List.exists (fn s => s = "--nolmbc") rawargs,
           target_dir = peek_chdir rawargs}
end

val (master_cline_options, cline_vars, targets) =
  getcline (CommandLine.arguments())

val clean_target_strings = ["clean", "cleanDeps", "cleanAll"]
val master_cleanp = List.exists (fn s => member s targets) clean_target_strings

val master_cline_nohmf =
    HM_Cline.default_options |> apply_updates master_cline_options

(* Captured after apply_updates so that any -C/--directory options
   have already taken effect and original_dir is the directory
   Holmake will treat as its starting point. *)
val original_dir = hmdir.curdir()
val originally_in_src = is_src_dir original_dir

(* Register a name->path mapping in holpathdb.  Idempotent re-registration
   (same vname → same path, e.g. when an upward walk discovers a project
   file already seen at startup) is silently accepted.  A collision
   (vname already registered to a different path) is fatal: the user has
   to resolve before we proceed. *)
fun register_holpath {vname,path} =
    case holpathdb.lookup_holpath {vname = vname} of
        NONE => holpathdb.extend_db {vname = vname, path = path}
      | SOME existing =>
          if existing = path then ()
          else die ("holproject.toml at " ^ path ^
                    " conflicts with prior registration of `" ^ vname ^
                    "` for " ^ existing)

fun read_holpathdb() =
    let
      val holpathdb_extensions =
          holpathdb.search_for_extensions (fn s => [])
            {starter_dirs = [FileSys.getDir()], skip = holpathdb.db_dirs()}
            handle Fail s => die s
      val _ = List.app register_holpath holpathdb_extensions
      open Holmake_types
      fun foldthis {vname,path} env = env_extend (vname, [LIT path]) env
    in
      holpathdb.fold foldthis (HM_BaseEnv.make_base_env master_cline_nohmf)
    end

val master_cline_option_value = #core master_cline_nohmf
val _ = if #force_lastmaker master_cline_option_value
        then set_lastmaker_force ()
        else ()
val usepfx = #jobs master_cline_option_value = 1
val {warn=warn0,info=info0,diag=diag0,...} =
      output_functions {chattiness = chattiness_level master_cline_option_value,
                        debug = #debug master_cline_option_value,
                        usepfx = usepfx}

(* Diag channels handed to ReadHMF parsing.  The info/warn fields are
   the same output_functions channels that respect -q/-v/-d, so any
   $(info)/$(warning) inside a Holmakefile naturally honours the
   command-line chattiness setting.  die is the unprefixed die_raw
   used by parser-internal "Bogus Holmakefile" failures; $(error)
   itself still raises HolmakeError, caught by Holmake.sml's top
   level. *)
val hmf_diags : internal_functions.diags =
    {info = info0, warn = warn0, die = die_raw}

val _ = diag0 "startup"
          (fn _ => "Started and have initial diagnostic/messaging functions")

(* execute pre-execs *)
val _ =
    if master_cleanp orelse #help master_cline_option_value then ()
    else
      let
        fun project_external_includes d =
            let val projfilename = OS.Path.concat (d, "holproject.toml")
            in
              if OS.FileSys.access(projfilename, [OS.FileSys.A_READ])
              then
                let
                  val _ = diag0 "startup"
                                (fn _ => "Consulting holproject.toml in " ^ d)
                  val config = HMProject.load{root=d}
                in
                  #external_includes config
                end handle Fail s => die ("Parse error in "^projfilename^": "^s)
              else []
            end
        val preexec_map =
            holpathdb.files_upward_in_hierarchy
              (fn d => ReadHMF.find_includes d @
                       project_external_includes d)
              {diag = diag0 "read-preexecs"}
              {filenames = [".hol_preexec"],
               starter_dirs = [FileSys.getDir()],
               skip = empty_strset}

        val _ = diag0 "startup"
                      (fn _ => "Read preexec_map, with " ^
                               Int.toString (Binarymap.numItems preexec_map) ^
                               " entries")
        val (msg,pfx) =
            if #no_preexecs master_cline_option_value then
              (info0, "Not executing")
            else (warn0, "Executing")
        val esc = String.translate (fn #"'" => "'\\''" | c => str c)
        fun appthis (k,(_, c0)) =
            let
              open Substring
              val c =
                  (if Systeml.OS = "winNT" then ""
                   else "HOLORIG="^esc (hmdir.toAbsPath original_dir) ^ " ") ^
                  string (dropr Char.isSpace (full c0))
              val _ =
                  msg (pfx ^ " " ^ OS.Path.concat(k,".hol_preexec") ^
                       ":\n  " ^ c)
      in
        if #no_preexecs master_cline_option_value then ()
        else
          let val _ = FileSys.chDir k
              val res = OS.Process.system c
          in
            if OS.Process.isSuccess res then hmdir.chdir original_dir
            else die "** FAILED"
          end
            end
      in
        Binarymap.app appthis preexec_map
      end

(* The hmftext is the form of the target as it appears in the Holmakefile *)
type tgt_ruledb = (dep, {hmftext: string, dependencies:dep list,
                         commands : quotation list})
                    Binarymap.dict
val empty_trdb : tgt_ruledb = Binarymap.mkDict hm_target.compare
type patrules = Holmake_types.patrules
val empty_patrules : patrules = Holmake_types.empty_patrules

(* Extend the base environment with vars passed at commandline (foldl below),
   as well as environment variables "magically" derived from other options,
   (handled by HM_Core_Cline.extend_env). *)
fun extend_with_cline_vars env =
    let val env =
            List.foldl (fn (vstr, env) =>
                           case String.fields (fn x => x = #"=") vstr of
                               [vname, contents] =>
                                 env_extend (vname, [LIT contents]) env
                             | _ => die ("Malformed variable assignment " ^
                                         "passed at commandline: " ^ vstr))
                       env
                       cline_vars
    in
      HM_Core_Cline.extend_env (#core master_cline_nohmf) env
    end


(* ----------------------------------------------------------------------
    get_hmf : unit -> "holmakefile data" (as per ReadHMF)

    Utility function to get the Holmakefile in the current directory, but
    using a cache so that any given file is only ever read once.
   ---------------------------------------------------------------------- *)

local
  open hm_target
  val base = extend_with_cline_vars (read_holpathdb())

  val hmcache = ref (Binarymap.mkDict String.compare)

  (* Dirs whose Holmakefile is safe for `local_rule_info' to consult
     when resolving a cross-directory target.  Populated as we read
     each Holmakefile: the dir it lives in is added, and so are every
     INCLUDES/PRE_INCLUDES entry that Holmakefile names.  This makes
     sibling-from-aggregator references work (Description's mdbook
     dep on `../Tutorial/labels.tsv' resolves because Manual's
     INCLUDES already named Tutorial) while leaving arbitrary
     prereq paths into unrelated dirs (e.g. a test fixture's
     `testd/Holmakefile' that lives outside any INCLUDES chain)
     untouched -- speculatively reading those would fire any
     `$(error ...)' in them.  Keyed by absolute path string to
     match `hmcache'. *)
  val known_dirs : string Binaryset.set ref =
      ref (Binaryset.empty String.compare)
  fun mark_known absdir =
      known_dirs := Binaryset.add(!known_dirs, absdir)
  fun mark_known_hmdirs ds =
      Binaryset.app (fn d => mark_known (hmdir.toAbsPath d)) ds

  (* Project context: detected once at startup from `original_dir`'s
     ancestor chain.  No per-dir lookup -- if `recursively` later
     wanders into a dir whose own holproject.toml differs (e.g. an
     aggregator like `parallel_builds/core` walks classical INCLUDES
     into another project), we do NOT activate that other project.
     That keeps the build deterministic and avoids ordering surprises
     when INCLUDES reaches into someone else's project tree.

     Project augmentation flows through `cline_incs` at the top-level
     `recursively` invocation: every discovered dir + external_include
     is added there, so the recursive walk visits them in classical
     post-order and each dir's graph nodes are added before cwd's hm
     dispatches the compile that references them. *)
  val project_config : HMProject.config option =
      if #no_project master_cline_option_value then NONE
      else
        case HMProject.find_root
               { start = hmdir.toAbsPath original_dir } of
            NONE => NONE
          | SOME root =>
            (SOME (HMProject.load { root = root })
             handle Fail msg =>
                    (warn0 ("holproject.toml at " ^ root ^
                            " ignored: " ^ msg);
                     NONE))

  val project_dirs : string list =
      case project_config of
          NONE => []
        | SOME cfg => HMProject.discover_dirs cfg

  val project_externals : string list =
      case project_config of
          NONE => []
        | SOME cfg => #external_includes cfg

  (* Every dir that build-time machinery treats as an implicit
     INCLUDES of every project dir.  Empty when project mode is off. *)
  val project_active_dirs : string list = project_dirs @ project_externals

  (* For find_rule's known-dirs gate: project dirs and their external
     includes can be consulted on demand for cross-dir rule lookup. *)
  val () = List.app mark_known project_active_dirs

  (* Fatal duplicate-name check across project dirs (HOL has no
     namespace separation, so any clash among reachable sources is
     ambiguous for `open Foo`).  Run once at startup; externals are
     not absorbed -- they live outside the project's source-namespace
     responsibility. *)
  val () =
      if null project_dirs then ()
      else
        case HMProject.find_name_clashes project_dirs of
            [] => ()
          | clashes =>
            let
              fun fmt (file, dirs) =
                  "  ambiguous source name '" ^ file ^ "' in:\n" ^
                  String.concat
                    (List.map (fn d => "    " ^ OS.Path.concat (d, file) ^
                                       "\n") dirs)
              val body = String.concat (List.map fmt clashes)
            in
              die ("holproject.toml: " ^
                   Int.toString (List.length clashes) ^
                   " ambiguous source name(s) reachable from this build:\n" ^
                   body ^
                   "Resolve by listing one of the offending directories in " ^
                   "the [exclude] key of holproject.toml (or in " ^
                   "[projects.<id>].exclude for a directory inside an " ^
                   "external project), or by renaming one of the files.")
            end

  (* One-shot diag block (visible under `-d project'). *)
  val () =
      case project_config of
          NONE =>
            if #no_project master_cline_option_value then
              diag0 "project"
                    (fn _ => "--no-project: skipping holproject.toml lookup")
            else
              diag0 "project"
                    (fn _ => "No holproject.toml found at or above " ^
                             hmdir.toAbsPath original_dir)
        | SOME cfg =>
          let
            val name = Option.getOpt (#name cfg, "<unnamed>")
            fun pmsg s = diag0 "project" (fn _ => s)
            fun plist label xs =
                pmsg ("  " ^ label ^ ": [" ^
                      String.concatWith ", " xs ^ "]")
            fun ext_to_str (e : HMProject.external_project) =
                #id e ^ " -> " ^ #path e
          in
            pmsg ("Project '" ^ name ^ "' rooted at " ^ #root cfg);
            plist "externals" (List.map ext_to_str (#externals cfg));
            List.app
              (fn {id, exclude, path = _} =>
                  if null exclude then ()
                  else plist ("external " ^ id ^ " exclude") exclude)
              (#externals cfg);
            plist "exclude" (#exclude cfg);
            plist "external_includes" project_externals;
            pmsg ("  discovered " ^
                  Int.toString (List.length project_dirs) ^
                  " project directories");
            List.app (fn d => pmsg ("    " ^ d)) project_dirs
          end

  (* Absolute excludes that apply when checking INCLUDES against the
     project's [exclude] / [projects.<id>].exclude lists. *)
  val project_excludes : string list =
      case project_config of
          NONE => []
        | SOME cfg =>
            #exclude cfg @
            List.concat (List.map #exclude (#externals cfg))
  (* Dirs for which we've already emitted a LOCAL_PARALLELISM_LIMIT
     warning, so we don't repeat it on every `limit_for_dir' call. *)
  val plimit_warned : string Binaryset.set ref =
      ref (Binaryset.empty String.compare)
  fun plimit_bad absdir s =
      "Holmakefile in " ^ absdir ^
      ": ignoring LOCAL_PARALLELISM_LIMIT = '" ^ s ^
      "' (need a single positive integer)"
  fun plimit_warn absdir s =
      if Binaryset.member(!plimit_warned, absdir) then ()
      else (plimit_warned := Binaryset.add(!plimit_warned, absdir);
            warn (plimit_bad absdir s))
  val default = (base,empty_trdb,empty_patrules,NONE)
  fun get_hmf0 d =
      if FileSys.access("Holmakefile", [FileSys.A_READ]) then
        let
          val (env, rdb, prs, tgt0) =
              ReadHMF.diagread hmf_diags
                               "Holmakefile"
                               (extend_with_cline_vars (read_holpathdb()))
              handle internal_functions.HolmakeError s => die_raw s
                   | Fail s =>
                     (die ("Bad Holmakefile in " ^ d ^ ": " ^ s);
                      (base,Binarymap.mkDict String.compare,
                       empty_patrules,NONE))
          fun hmfstr_to_tgt s = s |> filestr_to_tgt |> setHMF_text s
          fun foldthis (k,{commands,dependencies=deps0},A) =
              Binarymap.insert(A, filestr_to_tgt k,
                               {commands = commands, hmftext = k,
                                dependencies = map hmfstr_to_tgt deps0})
        in
          (env, Binarymap.foldl foldthis empty_trdb rdb, prs,
           Option.map filestr_to_tgt tgt0)
        end
      else
        default
in
fun get_hmf_for_dir absdir =
    case Binarymap.peek(!hmcache, absdir) of
        SOME r => (mark_known absdir; r)
      | NONE =>
        let
          val cur = FileSys.getDir()
          val need_chdir = cur <> absdir
          val () = if need_chdir then FileSys.chDir absdir else ()
          val (result as (env, _, _, _)) =
              get_hmf0 absdir
              handle e => (if need_chdir then FileSys.chDir cur else ();
                           raise e)
          val () = if need_chdir then FileSys.chDir cur else ()
          val dir_hm = hmdir.fromPath {origin = "", path = absdir}
          val incs = envlist hmf_diags env "INCLUDES" |> slist_to_dset dir_hm
          val pres = envlist hmf_diags env "PRE_INCLUDES" |> slist_to_dset dir_hm
        in
          hmcache := Binarymap.insert (!hmcache, absdir, result);
          mark_known absdir;
          mark_known_hmdirs incs;
          mark_known_hmdirs pres;
          result
        end

fun get_hmf () = get_hmf_for_dir (FileSys.getDir())
fun is_known_dir absdir = Binaryset.member(!known_dirs, absdir)

(* Project context, computed once at startup (see project_config and
   friends above).  All four bindings are derived from cwd's ancestor
   chain and stay constant for the rest of the Holmake run:
     project_active_dirs : list of dirs (project + external_includes)
       that act as implicit INCLUDES of every project dir;
     project_excludes   : absolute paths of project-tree dirs the
       config asks to skip;
     project_active_root: the project root, for diag messages. *)

(* first two bindings look redundant; this is to escape the local-in-end *)
val project_active_dirs = project_active_dirs
val project_excludes = project_excludes
val project_active_root = Option.map #root project_config
val project_modep = isSome project_config

(* `limit_for_dir' must not trigger a Holmakefile read here: doing
   so would chdir under code in `build_depgraph' that captures
   `FileSys.getDir()' for rule lookup.  We only consult `hmcache'
   directly.  If the dir's Holmakefile hasn't been read by the
   normal `recursively' traversal (e.g. foreign-external nodes such
   as sigobj references), we return NONE -- those nodes don't drive
   jobs in this Holmake, so the limit is moot. *)
fun limit_for_dir (d : hmdir.t) : int option =
    let val absdir = hmdir.toAbsPath d
    in
      case Binarymap.peek(!hmcache, absdir) of
          NONE => NONE
        | SOME (env, _, _, _) =>
          case envlist hmf_diags env "LOCAL_PARALLELISM_LIMIT" of
              [] => NONE
            | [s] =>
              (case Int.fromString s of
                   SOME n => if n > 0 then SOME n
                             else (plimit_warn absdir s; NONE)
                 | NONE => (plimit_warn absdir s; NONE))
            | ss => (plimit_warn absdir (String.concatWith " " ss); NONE)
    end
end

(* Compute INCLUDES + PRE_INCLUDES for `dir'.  Reads the Holmakefile
   via get_hmf(), then enforces the INCLUDES-vs-[exclude] consistency
   check: if the active project's [exclude] (or any external's
   exclude) names a dir that the Holmakefile explicitly INCLUDEs, die.
   The check fires only when project mode is active AND `dir' is a
   project dir; otherwise it's a no-op. *)
fun getnewincs dir =
    let
      val (env, _, _, _) = get_hmf()
      val raw_incs = envlist hmf_diags env "INCLUDES" |> slist_to_dset dir
      val raw_pres = envlist hmf_diags env "PRE_INCLUDES" |> slist_to_dset dir
      val abs_dir = hmdir.toAbsPath dir

      val excl_pfxset =
          List.foldl (fn (ex,fspt) => fspathTrie.insertPath ex fspt)
                     fspathTrie.empty
                     project_excludes
      fun check_one d =
          let val da = hmdir.toAbsPath d
          in
            case fspathTrie.hasPrefix excl_pfxset da of
                SOME pfx =>
                die ("\nHolmakefile in " ^ abs_dir ^
                     ": INCLUDES references \n  " ^ da ^
                     "\nbut that directory is subsumed by\n  " ^
                     "[exclude] " ^ pfx ^ "\nof the project at " ^
                     Option.getOpt (project_active_root, "?") ^
                     ".  Resolve the contradiction: either remove the " ^
                     "INCLUDES entry or remove the [exclude] entry.")
              | NONE => ()
          end
      val () = Binaryset.app check_one raw_incs
      val () = Binaryset.app check_one raw_pres
    in
      {includes = raw_incs, preincludes = raw_pres}
    end

(* Examining the c/line options, determine whether to use a
   Holmakefile at all, and which one if we are going to use one.
*)
val (cline_hmakefile, cline_nohmf) =
    List.foldl (fn (f,(hmf,nohmf)) =>
                   ((case #hmakefile f of NONE => hmf | SOME s => SOME s),
                    nohmf orelse #no_hmf f))
               (NONE,false)
               master_cline_options

fun get_hmf_cline_updates hmenv =
  let
    val hmf_cline = envlist hmf_diags hmenv "CLINE_OPTIONS"
    val (hmf_options, _, hmf_rest) = getcline hmf_cline
    val _ = if null hmf_rest then ()
            else
              warn ("Unused c/line options in makefile: "^
                    String.concatWith " " hmf_rest)
  in
    hmf_options
  end


val starting_holmakefile =
    if cline_nohmf then NONE
    else
      case cline_hmakefile of
          NONE => if exists_readable "Holmakefile" then SOME "Holmakefile"
                  else NONE
        | x => x

val (start_hmenv, start_rules, start_patrules, start_tgt) = get_hmf()

val start_envlist = envlist hmf_diags start_hmenv
val start_options = start_envlist "OPTIONS"

val option_value : HM_Cline.t =
    HM_Cline.default_options
      |> apply_updates (get_hmf_cline_updates start_hmenv)
      |> apply_updates master_cline_options
val coption_value = #core option_value
val cmdl_HOLDIR = #holdir coption_value
val HOLDIR    = case cmdl_HOLDIR of NONE => HOLDIR0 | SOME s => s
val SIGOBJ    = normPath(Path.concat(HOLDIR, "sigobj"));


(* things that need to be read out of the first Holmakefile, and which will
   govern the behaviour even when recursing into other directories that may
   have their own Holmakefiles *)
val (outputfns as {warn,tgtfatal,diag,info,chatty,info_inline,info_inline_end})=
    output_functions {chattiness = chattiness_level coption_value,
                      debug = #debug coption_value,
                      usepfx = usepfx}
val do_logging_flag = #do_logging coption_value
val no_lastmakercheck = #no_lastmaker_check coption_value
val show_usage = #help coption_value
val show_json = #json coption_value
val cline_cachekey = #cachekey coption_value
val cline_rebuild_strategy = #rebuild coption_value
val quit_on_failure = #quit_on_failure coption_value
val toplevel_no_prereqs = #no_prereqs coption_value
val toplevel_no_overlay = #no_overlay coption_value
val cline_additional_includes = #includes coption_value
val cline_always_rebuild_deps = #rebuild_deps coption_value
val cline_nobuild = #no_action coption_value
val cline_recursive_build = #recursive_build coption_value
val cline_recursive_clean = #recursive_clean coption_value
val cline_dirs = #dirs coption_value
val scan_output_functions =
    if isSome cline_cachekey orelse
       (show_json andalso chattiness_level coption_value <= 1) then
      quieten_info outputfns
    else outputfns

(* make the cline includes = [] so that these are only looked at once
   (when the cline_additional_includes value is folded into dirinfo values
   and eventually used in hm_recur).
*)
val pass_option_value =
    HM_Cline.fupd_core (HM_Core_Cline.fupd_includes (fn _ => [])) option_value

val _ = diag "startup" (fn _ => "CommandLine.name() = "^CommandLine.name())
val _ = diag "startup"
             (fn _ => "CommandLine.arguments() = "^
                      String.concatWith ", " (CommandLine.arguments()))

(* set up logging *)
val logfilename = Systeml.make_log_file
val hostname = if Systeml.isUnix then HostName.get () ^ "-" else ""

fun finish_logging buildok = let
in
  if do_logging_flag andalso FileSys.access(logfilename, []) then let
      open Date
      val timestamp = fmt "%Y-%m-%dT%H%M" (fromTimeLocal (Time.now()))
      val newname0 = hostname^timestamp
      val newname = (if buildok then "hmlog-good-" else "hmlog-bad-") ^ newname0
    in
      FileSys.rename {old = logfilename, new = newname}
    end
  else ()
end handle IO.Io _ => warn "Had problems making permanent record of make log"

val _ = Process.atExit (fn () => finish_logging false)

(* ----------------------------------------------------------------------

    recursively

    The hm parameter is how work is actually done; this parameter is
    called when all of the necessary recursion has been performed and
    work should be done in the current ("local") directory. (We are
    performing a post-order depth-first traversal.)

    Finally, what of the dirinfo?

    This record includes
        includes: the includes that the local directory knows about
                  (which will have come from the command-line or
                  INCLUDES lines in the local Holmakefile
     preincludes: similarly
         visited: a set of visited directories (with directories
                  expressed as absolute paths)

    The includes and preincludes are clearly useful when it comes time to
    do any local work, but also specify how the recursion is to happen.

    Now, the recursion into those directories may result in extra
    includes and preincludes.
   ---------------------------------------------------------------------- *)
fun idm_lookup idm key =
  case Binarymap.peek(idm, key) of
      NONE => {pres = empty_dirset, incs = empty_dirset}
    | SOME r => r

fun extend_idmap k (v as {incs = i,pres = p}) idm0 =
  case Binarymap.peek(idm0, k) of
      NONE => Binarymap.insert(idm0, k, v)
    | SOME {incs = i0, pres = p0} =>
        Binarymap.insert(idm0, k,
                         {incs = Binaryset.union(i0,i),
                          pres = Binaryset.union(p0,p)})

fun print_set ds =
  "{" ^ set_concatWith hmdir.pretty_dir ", " ds ^ "}"

type incmap = (hmdir.t, {incs:dirset,pres:dirset}) Binarymap.dict
type dirinfo = {incdirmap : incmap, visited : hmdir.t Binaryset.set,
                ancestors : hmdir.t list (* most recent hd of list *)}
type 'a hmfold =
     {includes : string list, preincludes : string list} ->
     (string -> unit) ->
     hmdir.t ->
     'a -> 'a

fun find_upto cmp pfx x els =
    case els of
        [] => NONE
      | h::t => if cmp (h,x) = EQUAL then SOME (h::pfx)
                else find_upto cmp (h::pfx) x t
(* ----------------------------------------------------------------------

    Parameters
           getnewincs : get INCLUDES information from a directory,
                        type : dir -> dirinfo

           {warn : how to issue a warning,
            diag : how to issue a diagnostic,
            hm   : what to do in a given directory;
                   will be either to build a graph, or to perform a clean
            dirinfo : tracks INCLUDES info, and the progress of the
                      recursion
            dir : the directory I'm in,
            data : the value to fold hm over, a graph for a normal build,
                   or just unit for a clean}

    Assume that we are already in directory dir, and will end in the same
    directory.

   ---------------------------------------------------------------------- *)
fun 'a recursively getnewincs dsopt {outputfns,verb,hm,dirinfo,dir,data} =
let
  val {incdirmap,visited,ancestors} = dirinfo : dirinfo
  val hm : 'a hmfold = hm
  val {warn,diag,info,chatty,info_inline_end, info_inline,...} : output_functions =
      outputfns
  val {includes=incset, preincludes = preincset} = getnewincs dir
  val incdirmap =
      incdirmap |> extend_idmap dir {incs = incset, pres = preincset}
                |> (case dsopt of
                        SOME ds => extend_idmap dir {incs=ds,pres=empty_dirset}
                      | NONE => (fn x => x))
  val recur_into = set_union (set_union incset preincset)
                             (case dsopt of NONE => empty_dirset
                                          | SOME ds => ds)
  fun recur_abbrev dir data (dirinfo:dirinfo) =
      recursively getnewincs NONE
                  {outputfns = outputfns,verb=verb,hm=hm,dirinfo=dirinfo,
                   dir=dir, data=data}
  val diag = diag "builddepgraph"
  val _ = diag (fn _ => "recursively: call in " ^ hmdir.pretty_dir dir)
  val _ = diag (fn _ => "recursively: includes (pre- & normal) = [" ^
                        set_concatWith hmdir.pretty_dir ", " recur_into ^ "]")
  val _ = diag (fn _ =>
                   "recursively: incdmap on dir " ^ hmdir.pretty_dir dir ^
                   " = " ^ print_set (#incs (idm_lookup incdirmap dir)))
  val _ = diag (fn _ =>
                   "recursively: ancestor chain = " ^
                   String.concatWith ", " (map hmdir.pretty_dir ancestors))
  fun recurse (acc as {visited,incdirmap,data:'a}) newdir = let
    val _ =
        case find_upto hmdir.compare [newdir] newdir ancestors of
            NONE => ()
          | SOME badchain =>
            let
              val diag = if verb = "Cleaning" then warn
                         else (fn s => (#tgtfatal outputfns s;
                                        OS.Process.exit OS.Process.failure))
            in
              diag ("\nINCLUDES chain loops:\n  " ^
                    String.concatWith " -->\n  "
                                      (map hmdir.pretty_dir badchain))
            end
  in
    if Binaryset.member(visited, newdir) then
      (* even if you don't want to rebuild newdir, you still want to learn
         about what it depends on so that the dependency map for this directory
         is appropriately augmented *)
      {visited = visited,
       data = data,
       incdirmap = extend_idmap dir (idm_lookup incdirmap newdir) incdirmap}
    else let
      val _ = FileSys.access
                (hmdir.toAbsPath newdir, [FileSys.A_READ, FileSys.A_EXEC])
              orelse
                die ("Attempt to recurse into non-existent directory: " ^
                     hmdir.pretty_dir newdir ^
                     "\n  (Probably a result of bad INCLUDES spec.)")
      val _ = diag (fn _ => "recursively: Visited set = " ^ print_set visited)
      val _ = FileSys.chDir (hmdir.toAbsPath newdir)
      val _ = write_lastmaker_in_cwd outputfns
      val result =
          case recur_abbrev newdir data
                            {incdirmap=incdirmap, visited=visited,
                             ancestors = newdir :: ancestors}
           of
              {visited,incdirmap = idm0,data=data'} =>
              {visited = visited,
               incdirmap = extend_idmap dir (idm_lookup idm0 newdir) idm0,
               data = data'}
      val _ = FileSys.chDir (hmdir.toAbsPath dir)
    in
      case result of
          {visited,incdirmap,data} =>
          let
            val {incs,pres} = idm_lookup incdirmap dir
          in
            diag (fn () =>
                     "recursively: computed includes for " ^
                     hmdir.pretty_dir dir ^ " = " ^ print_set incs);
            diag (fn () =>
                     "recursively: computed pre-includes for " ^
                     hmdir.pretty_dir dir ^ " = " ^ print_set pres)
          end;
      result
    end
  end
  fun do_em (accg as {incdirmap,data:'a,visited}) dirs =
      case dirs of
          [] =>
          let
            val {pres, incs} = idm_lookup incdirmap dir
            val f = Binaryset.foldr (fn (d,acc) => hmdir.toAbsPath d :: acc) []
            val _ = if not (isSome dsopt) then
                      info_inline (verb ^ " " ^ bold (hmdir.pretty_dir dir))
                    else ()
            val data' = hm {includes=f incs,preincludes=f pres} warn dir data
          in
            {incdirmap = incdirmap, visited = visited, data = data'}
          end
        | x::xs => do_em (recurse accg x) xs
  val visited = Binaryset.add(visited, dir)
  val result =
      do_em {visited = visited, incdirmap = incdirmap, data = data}
            (Binaryset.listItems recur_into)
in
  diag (fn _ => "recursively: Finished work in "^hmdir.pretty_dir dir);
  result
end

(* prepare to do logging *)
val () = if do_logging_flag then
           if FileSys.access (logfilename, []) then
             warn "Make log exists; new logging will concatenate on this file"
           else let
               (* touch the file *)
               val outs = openOut logfilename
             in
               closeOut outs
             end handle IO.Io _ => warn "Couldn't set up make log"
         else ()

val actual_overlay =
    if toplevel_no_overlay orelse member "NO_OVERLAY" start_options then NONE
    else SOME DEFAULT_OVERLAY

val std_include_flags = [SIGOBJ]

fun get_rule_info rdb env tgt =
    case Binarymap.peek(rdb, tgt) of
      NONE => NONE
    | SOME {dependencies, commands, hmftext} =>
      let
        fun special tgt' =
            valOf (hm_target.HMF_text tgt')
            handle Option =>
                   die ("No Holmakefile text for " ^ tgt_toString tgt' ^
                        " in rule for " ^ tgt_toString tgt)
        val dep1 = [LIT (special (hd dependencies))] handle Empty => [LIT ""]
        val env = env |> env_extend("<", dep1)
                      |> env_extend("@", [LIT hmftext])
      in
        SOME {dependencies = dependencies,
              commands = map (perform_substitution hmf_diags env) commands}
      end

(* Look up the rule for `t`.  A rule belongs to whichever Holmakefile
   was being parsed when it was registered, NOT necessarily the dir
   that holds the target file -- e.g. `src/proofman/Holmakefile' has
   a rule for `$(HOLDIR)/bin/hol.state0' (target dirpart = bin/),
   but the rule lives in proofman's rdb.

   So: try cwd's Holmakefile first (the rule-defining file is
   typically cwd while `recursively' descends through it).  Only if
   that misses, and the target's dirpart is part of this build's
   INCLUDES closure, consult the target's home Holmakefile -- this
   is the cross-manual `SIBLING_LABELS' case where Tutorial's
   Holmakefile has the rule for `Tutorial/labels.tsv' but it's
   referenced from Description's mdbook recipe.

   The closure gate (`is_known_dir') keeps us from speculatively
   reading a stranger Holmakefile that happens to lie under a
   referenced path (a test fixture's `testd/Holmakefile' whose
   `$(error ...)' would otherwise abort the build).

   If both rdbs claim the same target, die: we have no principled
   precedence to resolve such a conflict, and silently picking one
   of two real recipes is a footgun.  Returns the rule paired with
   the dir of the Holmakefile that owns it (used by `build_depgraph'
   to set `node.dir' and the env feeding GraphExtra). *)
fun find_rule t =
    let
      val (cwd_env, cwd_rules, _, _) = get_hmf()
      val cwd_dir = hmdir.curdir()
      val cwd_abs = hmdir.toAbsPath cwd_dir
      val tgt_dir = hm_target.dirpart t
      val tgt_dir_abs = hmdir.toAbsPath tgt_dir
      val cwd_has = isSome (Binarymap.peek(cwd_rules, t))
      val home_data =
          if is_known_dir tgt_dir_abs andalso tgt_dir_abs <> cwd_abs
          then SOME (get_hmf_for_dir tgt_dir_abs)
          else NONE
      val home_has =
          case home_data of
              NONE => false
            | SOME (_, rules', _, _) => isSome (Binarymap.peek(rules', t))
    in
      if cwd_has andalso home_has then
        die ("Conflicting rules for `" ^ tgt_toString t ^
             "': defined in both " ^ hmdir.pretty_dir cwd_dir ^
             "/Holmakefile and " ^ hmdir.pretty_dir tgt_dir ^
             "/Holmakefile.\n" ^
             "Remove one of the duplicates.")
      else if cwd_has then
        Option.map (fn r => (r, cwd_dir))
                   (get_rule_info cwd_rules cwd_env t)
      else if home_has then
        (case home_data of
            SOME (env', rules', _, _) =>
              Option.map (fn r => (r, tgt_dir))
                         (get_rule_info rules' env' t)
          | NONE => NONE)
      else NONE
    end

fun local_rule_info t = Option.map #1 (find_rule t)

(* Returns the directory that actually holds the rule for `t' (the
   home of the Holmakefile its recipe lives in), or `hmdir.curdir()'
   when no rule exists anywhere in scope.  Used by `build_depgraph'
   to set `node.dir' (the cwd ProcessMultiplexor uses for recipe
   execution) and the env that feeds GraphExtra. *)
fun rule_home t =
    case find_rule t of
        SOME (_, d) => d
      | NONE => hmdir.curdir()

(* Pattern-rule lookup applies to any target at or below the
   Holmakefile's directory: a pattern with a literal directory
   prefix (e.g. `sub/%.tex : sub/%.smd') matches targets in the
   named subdirectory, and a bare pattern (e.g. `%.tex') matches
   targets anywhere under the Holmakefile (the stem then absorbs
   any directory separators).  Targets in parent or sibling
   directories of the Holmakefile aren't reachable from this
   ruleset and yield NONE.

   The matcher takes the target's path relative to the
   Holmakefile's directory; substituted dep strings come back the
   same way and lift through `filestr_to_tgt' (whose `hmdir.extendp'
   already handles directory components correctly).

   `can_make' implements GNU make's two-phase implicit-rule search:
   a pattern rule is only applicable when every substituted prereq
   either exists on disk or has an exact rule that builds it.
   Without this guard a pattern like `%.tex: %.stex' would claim
   every .tex target in the directory, including hand-maintained
   ones whose .stex source doesn't exist. *)
fun rel_to_curdir t =
    let
      val cwd_abs = hmdir.toAbsPath (hmdir.curdir())
      val tgt_dir_abs = hmdir.toAbsPath (hm_target.dirpart t)
      val tgt_file = fromFile (hm_target.filepart t)
    in
      if tgt_dir_abs = cwd_abs then SOME tgt_file
      else if String.isPrefix (cwd_abs ^ "/") tgt_dir_abs then
        SOME (String.extract (tgt_dir_abs, size cwd_abs + 1, NONE)
              ^ "/" ^ tgt_file)
      else NONE
    end
fun pattern_rule_info t =
    case rel_to_curdir t of
        NONE => NONE
      | SOME tgt_s =>
        let
          val (env, rules, prs, _) = get_hmf()
          fun can_make dep_s =
              exists_readable dep_s orelse
              isSome (Binarymap.peek (rules, filestr_to_tgt dep_s))
        in
          case match_pattern_rules hmf_diags can_make env prs tgt_s of
              NONE => NONE
            | SOME {dependencies, commands} =>
              SOME {dependencies = map filestr_to_tgt dependencies,
                    commands = commands}
        end

fun extra_deps t =
      Option.map #dependencies (local_rule_info t)
fun localstr_extra_deps s =
    extra_deps (hm_target.mk(hmdir.curdir(), toFile s))

fun isPHONY t =
    case localstr_extra_deps ".PHONY" of
        NONE => false
      | SOME l => List.exists (fn e => hm_target.compare(e,t) = EQUAL) l

fun extra_commands t = Option.map #commands (local_rule_info t)

fun extra_targets() =
    let
      val (_, rules, _, _) = get_hmf()
    in
      Binarymap.foldr (fn (k,_,acc) => k::acc) [] rules
    end

(* extra_rule_for combines the exact-match rule for t (if any) with
   a matching pattern rule (if any), respecting GNU make's precedence:
   - an exact rule with commands wins outright;
   - otherwise, if a pattern rule matches, its commands fire and its
     deps union with any deps from a recipe-less exact rule;
   - otherwise the exact rule's deps-only entry (if any) is returned
     unchanged.  Pattern rules are scoped to the current Holmakefile's
     directory tree: they can match targets in subdirectories of cwd
     (via a literal prefix like `sub/%.x' or via the bare `%.x' whose
     stem absorbs `/'), but not in parent or sibling directories. *)
fun extra_rule_for t =
    let
      val exact = local_rule_info t
    in
      case exact of
          SOME {commands = _ :: _, ...} => exact
        | _ =>
          case pattern_rule_info t of
              NONE => exact
            | SOME {dependencies = pat_deps, commands = pat_cmds} =>
              let
                val ex_deps =
                    case exact of
                        SOME {dependencies, ...} => dependencies
                      | NONE => []
              in
                SOME {dependencies = ex_deps @ pat_deps, commands = pat_cmds}
              end
    end
fun dir_varying_envlist s =
    let val (env, _, _, _) = get_hmf()
    in
      envlist hmf_diags env s
    end

fun extra_cleans() = dir_varying_envlist "EXTRA_CLEANS"

(*** Compilation of files *)
val binfo : HM_Cline.t BuildCommand.buildinfo_t =
    {optv = option_value,
     actual_overlay = actual_overlay, envlist = dir_varying_envlist,
     hmenv = start_hmenv,
     quit_on_failure = quit_on_failure, outs = outputfns,
     SIGOBJ = SIGOBJ}
val {extra_impl_deps,build_graph} = BuildCommand.make_build_command binfo

val _ = let
in
  diag "startup" (fn _ => "HOLDIR = "^HOLDIR);
  diag "startup" (fn _ => "Targets = [" ^ String.concatWith ", " targets ^ "]");
  diag "startup" (fn _ => "Additional includes = [" ^
                          String.concatWith ", "
                                            cline_additional_includes ^ "]");
  diag "startup" (fn _ => "Additional Holmake variables = [" ^
                          String.concatWith "," cline_vars ^ "]");
  diag "startup" (fn _ => HM_BaseEnv.debug_info option_value)
end

(** Top level sketch of algorithm *)
(*

   We have the following relationship --> where this arrow should be read
   "leads to the production of in one step"

    *.sml --> *.uo                          [ mosmlc -c ]
    *.sig --> *.ui                          [ mosmlc -c ]
    *Script.uo --> *Theory.sig *Theory.sml
       [ running the *Script that can be produced from the .uo file ]
    *Script.uo --> *.art
       [ running the *Script with proof-recording enabled ]
    *.art --> *.ot.art
       [ opentheory info --article ]

   (where I have included the tool that achieves the production of the
   result in []s)

   However, not all productions can go ahead with just the one principal
   dependency present.  Sometimes other files are required to be present
   too.  We don't know which other files which are required, but we can
   find out by using Ken's holdep tool.  (This works as follows: given the
   name of the principal dependency for a production, it gives us the
   name of the other dependencies that exist in the current directory.)

   In theory, we could just run holdep everytime we were invoked, and
   with a bit of luck we'll design things so it does look as if really
   are computing the dependencies every time.  However, this is
   unnecessary work as we can cache this information in files and just
   read it in from these.  Of course, this introduces a sub-problem of
   knowing that the information in the cache files is up-to-date, so
   we will need to compare time-stamps in order to be sure that the
   cached dependency information is up to date.

   Another problem is that we might need to build a dependency DAG but
   in a situation where elements of the principal dependency chain
   were themselves out of date.
*)

(* The primary dependency chain does not depend on anything in the
   file-system; it always looks the same.  However, additional
   dependencies depend on what holdep tells us.  This function that
   runs holdep, and puts the output into specified file, which will live
   in DEPDIR somewhere. *)

fun get_implicit_dependencies incinfo (f: File) : dep Binaryset.set = let
  val {preincludes,includes} = incinfo
  val file_dependencies0 =
      get_direct_dependencies {incinfo = incinfo,
                               extra_targets = extra_targets(),
                               output_functions = outputfns,
                               DEPDIR = DEPDIR} f
  val diag = diag "impdeps"
  val _ = diag (fn _ => "get_implicit_dependencies("^fromFile f^"), " ^
                        "directdeps = " ^ pdlist file_dependencies0)
  val file_dependencies =
      case actual_overlay of
        NONE => file_dependencies0
      | SOME s => if isSome (holdep_arg f) then
                    filestr_to_tgt (fullPath [SIGOBJ, s]) :: file_dependencies0
                  else
                    file_dependencies0
  fun requires_exec (SML (Theory _)) = true
    | requires_exec (SIG (Theory _)) = true
    | requires_exec (ART (RawArticle _)) = true
    | requires_exec (DAT _) = true
    | requires_exec _                = false
in
  if requires_exec f then let
      (* because we have to build an executable in order to build a
         theory, this build depends on all of the dependencies
         (meaning the transitive closure of the direct dependency
         relation) in their .UO form, not just .UI *)
      val get_direct_dependencies =
          get_direct_dependencies {incinfo = incinfo, DEPDIR = DEPDIR,
                                   output_functions = outputfns,
                                   extra_targets = extra_targets()}
      val starters = get_direct_dependencies f
      (* ignore theories as we don't want to depend on the script files
         behind them *)
      fun collect_all_dependencies sofar tovisit =
          case tovisit of
            [] => sofar
           | d::ds =>
             case hm_target.filepart d of
                 UO (Theory _) => collect_all_dependencies sofar ds
               | UI (Theory _) => collect_all_dependencies sofar ds
               | _ =>
                 let
                   open hm_target
                   val deps =
                       (* Cross-dir deps don't recurse here -- their
                          transitive closure is recorded in the dep
                          graph by build_depgraph's external branch. *)
                       if hmdir.compare(dirpart d, hmdir.curdir()) <> EQUAL
                       then []
                       else
                         case filepart d of
                             UI x => (get_direct_dependencies f @
                                      get_direct_dependencies (UO x))
                           | _ => get_direct_dependencies f
                   val newdeps = set_diff (deplist_to_set deps) sofar
                 in
                   collect_all_dependencies (set_union sofar newdeps)
                                            (listItems newdeps @ ds)
                 end
      val tcdeps = collect_all_dependencies (deplist_to_set starters) starters
      val _ = diag (fn _ => "get_implicit_dependencies("^fromFile f^"), " ^
                            "tcdeps = " ^
                            set_concatWith tgt_toString ", " tcdeps)
      val uo_deps =
          Binaryset.foldl
            (fn (d, A) => case hm_target.filepart d of
                              UI x => set_add (hm_target.setFile (UO x) d) A
                            | _ => A)
            hm_target.empty_tgtset
            tcdeps
      val alldeps = set_addList (file_dependencies @ extra_impl_deps)
                                (set_union tcdeps uo_deps)
    in
      alldeps
    end
  else
    deplist_to_set file_dependencies
end

fun get_explicit_dependencies (f:File) : dep list =
    let
      val result = case extra_deps (filestr_to_tgt (fromFile f)) of
                       SOME deps => deps
                     | NONE => []
    in
      diag "expdeps" (fn _ => fromFile f ^ " -explicitdeps-> " ^ pdlist result);
      result
    end

val slist_to_depset =
    List.foldl (fn (s,set) => Binaryset.add(set, filestr_to_tgt s))
               hm_target.empty_tgtset
fun dset_union ds1 ds2 =
    Binaryset.listItems
      (Binaryset.union(deplist_to_set ds1, deplist_to_set ds2))



(** Build graph *)

exception CircularDependency
exception BuildFailure
exception NotFound

fun no_extra_rule tgtopt =
    case tgtopt of
        NONE => true
      | SOME tgt => not (isSome (extra_commands tgt))
fun no_full_extra_rule tgtopt =
    case tgtopt of
        NONE => true
      | SOME tgt => case extra_commands tgt of NONE => true | SOME cl => null cl

val done_some_work = ref false
open HM_DepGraph

fun is_script s =
  case toFile s of
      SML (Script _) => true
    | _ => false

fun de_script s =
  case toFile s of
      SML (Script s) => SOME s
    | _ => NONE

type cdelem = hmdir.t * string
type cdset = cdelem Binaryset.set * cdelem list
val empty_cdset =
    (Binaryset.empty (pair_compare(hmdir.compare, String.compare)), [])
fun cdset_add (set,stk) e = (Binaryset.add(set,e), e::stk)
fun cdset_member(set,stk) e = Binaryset.member(set,e)
fun cdset_toString ((_,stk):cdset) =
    String.concatWith ">" (map #2 (List.rev stk))

(* Read a cross-directory dep's source-directory depfile (without
   rerunning holdep) and return its parsed deps.  The dep's [dirpart]
   is typically sigobj (uploads symlink products there) but depfiles
   live next to the actual sources; resolve the symlink to find the
   real source directory. *)
fun read_foreign_depfile tgt =
    case holdep_arg (hm_target.filepart tgt) of
        NONE => []
      | SOME arg =>
        let
          val abs_path = hm_target.toString tgt
          val fs_path =
              case HFS_NameMunge.HOLtoFS abs_path of
                  NONE => abs_path
                | SOME {fullfile, ...} => fullfile
          val real_objpath = OS.FileSys.realPath fs_path
                             handle OS.SysErr _ => fs_path
          val objdir_arcs_rev =
              List.rev (#arcs (OS.Path.fromString HFS_NameMunge.HOLOBJDIR))
          fun stripPrefix [] xs = SOME xs
            | stripPrefix _ [] = NONE
            | stripPrefix (p::ps) (x::xs) =
                if p = x then stripPrefix ps xs else NONE
          fun strip_hol_objs p =
              let val {isAbs, vol, arcs} = OS.Path.fromString p
                  val rev_arcs = List.rev arcs
              in case rev_arcs of
                     [] => NONE
                   | _ :: rest =>
                     Option.map
                       (fn rest' =>
                           OS.Path.toString
                             {isAbs=isAbs, vol=vol,
                              arcs=List.rev rest'})
                       (stripPrefix objdir_arcs_rev rest)
              end
        in
          case strip_hol_objs real_objpath of
              NONE => []
            | SOME real_srcdir =>
              let
                val foreign_depdir =
                    OS.Path.concat (real_srcdir, DEPDIR)
                val depfile = mk_depfile_name foreign_depdir
                                              (fromFile arg)
                val foreign_hmdir =
                    hmdir.extendp {base = hmdir.curdir(),
                                   extension = real_srcdir}
              in
                if exists_readable depfile then
                  get_dependencies_from_file_in_dir
                    foreign_hmdir depfile
                else []
              end
        end

(* is run in a directory at a time *)
type g = GraphExtra.t HM_DepGraph.t
fun build_depgraph cdset incinfo (tgt:dep) g0:(g * node) =
let
  val dir = hm_target.dirpart tgt and target = hm_target.filepart tgt
  val {preincludes,includes} = incinfo
  (* Project augmentation: project_active_dirs is empty unless a
     holproject.toml was detected at startup, in which case it lists
     every project dir + external_include so Holdep can resolve
     unqualified `open Foo' references to a Foo.{sml,sig} living in
     any project directory.  Appended last so explicit INCLUDES still
     win on name clashes. *)
  val incinfo = {preincludes = preincludes,
                 includes = includes @ std_include_flags @
                            project_active_dirs}
  val pdep = primary_dependent target
  val target_s = tgt_toString tgt
  val actual_dir = hmdir.curdir()
  fun fp d s = hmdir.extendp {base = d, extension = s}
  fun fps d = hmdir.toAbsPath d
  fun addF tgt n = (n,tgt)
  fun nstatus g n = peeknode g n |> valOf |> #status
  fun build (tgt':dep) g =
    build_depgraph (cdset_add cdset (dir, target_s)) incinfo tgt' g

  val fullpath = fp dir target_s
  val fullpath_s = fps fullpath
  val pretty_tgt = hmdir.pretty_dir fullpath
  (* `rh' is the dir of the Holmakefile that actually carries the
     rule for `tgt' -- cwd in the usual case, the target's home dir
     when this is a cross-manual SIBLING_LABELS dep that's resolved
     via the target's home rdb.  Used both for the env that feeds
     GraphExtra (HOLHEAP etc. should come from the rule's Holmakefile,
     not from whoever happens to reference the target) and for
     `node.dir' (the cwd ProcessMultiplexor chdir's into before
     running the recipe). *)
  val rh = rule_home tgt
  val (env, _, _, _) = get_hmf_for_dir (hmdir.toAbsPath rh)
  val extra = GraphExtra.get_extra { master_dir = original_dir,
                                     master_cline = option_value,
                                     envlist = envlist hmf_diags env }
  val extra_deps = if GraphExtra.canIgnore tgt extra then []
                   else GraphExtra.extra_deps extra
  val diag = fn f => diag "builddepgraph"
                          (fn _ => "|" ^ cdset_toString cdset ^ "| " ^ f ())
  val _ = diag (fn _ => "Target = " ^ pretty_tgt)
  val _ = diag (fn _ => "Extra = " ^ GraphExtra.toString extra)
  val _ = not (cdset_member cdset (dir,target_s)) orelse
          die (pretty_tgt ^ " seems to depend on itself failing\n" ^
               " Loop is : " ^ cdset_toString cdset ^ ">" ^ pretty_tgt)
  fun buildNodeInfo g0 =
      if isSome pdep andalso no_full_extra_rule (SOME tgt) then
        let
          val pdep = hm_target.mk(dir, valOf pdep)
          val (g1, pnode) = build pdep g0
          val _ = diag (fn _ => "Extended graph with primary dependency for " ^
                                target_s)
          val secondaries =
              set_addList (get_explicit_dependencies target)
                          (get_implicit_dependencies incinfo target)
                          |> set_addList extra_deps
          val _ = diag (fn _ => target_s ^ " -secondaries-> " ^
                                set_concatWith tgt_toString ", " secondaries)
          fun foldthis (d, (g, secnodes)) =
              let
                val (g', n) = build d g
              in
                (g', addF d n::secnodes)
              end
          val (g2, depnodes : (HM_DepGraph.node * dep) list) =
              Binaryset.foldl foldthis (g1, [addF pdep pnode]) secondaries
          val unbuilt_deps =
              List.filter (fn (n,_) => let val stat = nstatus g2 n
                                       in
                                         is_pending stat orelse is_failed stat
                                       end)
                          depnodes
          val bic = case toFile target_s of
                        SML (Theory s) => BIC_BuildScript s
                      | SIG (Theory s) => BIC_BuildScript s
                      | DAT s => BIC_BuildScript s
                      | _ => BIC_Compile
          (* For theory targets, when --rebuild=cachekey is in force,
             consult the cachekey stamp next to the .dat instead of
             mtime.  Short-circuit to Succeeded when the target exists
             on disk and the stamp records the current input hash. *)
          fun theory_stamp_path thy =
              let
                val datHOL_s = fps (fp dir (thy ^ "Theory.dat"))
                val datFS =
                    case HFS_NameMunge.HOLtoFS datHOL_s of
                        SOME {fullfile, ...} => fullfile
                      | NONE => datHOL_s
              in
                HM_Cachekey.stamp_path_for_datfile datFS
              end
          fun stamp_matches g thy =
              case HM_Cachekey.read_stamp (theory_stamp_path thy) of
                  NONE => (false, g)
                | SOME recorded =>
                  let val (ck, g') =
                          HM_Cachekey.compute_for_deps g
                                                       (map #2 depnodes)
                  in
                    case ck of
                        HM_Cachekey.Key k => (k = recorded, g')
                      | HM_Cachekey.Missing _ => (false, g')
                  end
          (* If this target is a theory's compile product (fooTheory.uo
             or fooTheory.ui), check the corresponding .dat node.
             Theory compile products are built alongside the .dat from
             the same script; under --rebuild=cachekey, when the .dat
             node is Succeeded, the products inherit that status --
             bypassing the mtime check that can spuriously fire on
             parallel-built siblings whose mtimes can race against
             each other. *)
          fun theory_dat_succeeded () =
              let
                val thy_opt = case hm_target.filepart tgt of
                                  UO (Theory s) => SOME s
                                | UI (Theory s) => SOME s
                                | _ => NONE
              in
                case thy_opt of
                    NONE => false
                  | SOME s =>
                    (case HM_DepGraph.target_node g2 (hm_target.mk(dir, DAT s)) of
                         NONE => false
                       | SOME n =>
                         (case HM_DepGraph.peeknode g2 n of
                              SOME {status = Succeeded, ...} => true
                            | _ => false))
              end
          val (cachekey_uptodate, g3) =
              if cline_rebuild_strategy <> HM_Cachekey_dtype.Cachekey then
                (false, g2)
              else
                (case bic of
                     BIC_BuildScript thy =>
                     if exists_readable fullpath_s andalso
                        null unbuilt_deps
                     then stamp_matches g2 thy
                     else (false, g2)
                   | BIC_Compile =>
                     if exists_readable fullpath_s andalso
                        null unbuilt_deps andalso
                        theory_dat_succeeded ()
                     then (true, g2)
                     else (false, g2))
          val needs_building =
              not cachekey_uptodate andalso
              (not (null unbuilt_deps) orelse
               set_exists (fn d => d depforces_update_of tgt)
                          (set_add pdep secondaries))
          val _ = if cachekey_uptodate then
                    diag (fn _ => target_s ^
                                  ": cachekey matches stamp, up-to-date")
                  else ()
        in
          ({target = tgt, seqnum = 0, phony = false,
            status = if needs_building then Pending{needed=false}
                     else Succeeded,
            extra = extra,
            mtime = hm_target.tgt_modTime tgt,
            local_parallelism_limit = limit_for_dir rh,
            command = BuiltInCmd (bic,incinfo), dir = rh,
            dependencies = depnodes }, g3)
        end
      else
        case extra_rule_for tgt of
            NONE => (
              diag (fn _ => "No extra info/rule for target " ^ target_s);
              ({target = tgt, seqnum = 0, phony = false,
                status = if exists_readable target_s then Succeeded
                         else Failed{needed=false},
                command = NoCmd, dir = rh, extra = extra,
                mtime = hm_target.tgt_modTime tgt,
                local_parallelism_limit = limit_for_dir rh,
                dependencies = []}, g0)
            )
          | SOME {dependencies, commands, ...} =>
            let
              val _ = diag (fn _ => target_s ^ " has rule")
              fun foldthis (d, (g, secnodes)) =
                let
                  val (g, n) = build d g
                in
                  (g, addF d n::secnodes)
                end
              fun depfoldthis (dep, (starp, deps)) =
                  let
                    open hm_target
                    val d = dirpart dep and f = filepart dep
                  in
                    case f of
                        SML (Script s) =>
                        if String.sub(s,0) = #"*" then
                          if isSome starp then
                            die
                              ("Multiple starred script dependencies for "^
                               target_s)
                          else if hmdir.compare(d, actual_dir) <> EQUAL then
                            die "Don't star non-local script files"
                          else
                            let
                              val s' = String.extract(s,1,NONE)
                            in
                              (SOME s',
                               (mk(d, SML (Script s')) |> setHMF_text s') ::
                               deps)
                            end
                        else (starp, dep :: deps)
                      | _ => (starp, dep :: deps)
                  end
              val (starred_dep, dependencies) =
                  if null commands then
                    List.foldr depfoldthis (NONE, []) dependencies
                  else (NONE, dependencies)
              val _ = case starred_dep of
                          SOME s =>
                            diag (fn _ => target_s ^ " has star = " ^ s)
                        | NONE => diag (fn _ => "No star for " ^ target_s)

              val more_deps =
                  case starred_dep of
                      NONE => hm_target.empty_tgtset
                    | SOME s =>
                        get_implicit_dependencies
                          incinfo
                          (SML(Theory s))
                          handle Option => die "more_deps invariant failure"
                               | e => die (
                                       "Unexpected exception: " ^
                                       General.exnMessage e ^
                                       " thrown in get_implicit_dependencies"
                                     )

              val (g1, depnodes) =
                  Binaryset.foldl foldthis (g0, [])
                                  (more_deps |> set_addList dependencies
                                             |> set_addList extra_deps)

              val unbuilt_deps =
                  List.filter
                    (fn (n,_) => let val stat = nstatus g1 n
                                 in
                                   is_pending stat orelse is_failed stat
                                 end)
                    depnodes
              val is_phony = isPHONY tgt
              val _ = if is_phony then diag (fn _ => target_s ^" is phony")
                      else ()
              val needs_building_by_deps_existence =
                  not (FileSys.access(target_s, [])) orelse
                  not (null unbuilt_deps) orelse
                  List.exists (fn d => d depforces_update_of tgt)
                              dependencies orelse
                  is_phony
              val needs_building =
                  needs_building_by_deps_existence andalso
                  not (null commands)
              val _ = if is_phony then
                        diag (fn _ => target_s ^ " needs building = " ^
                                      Bool.toString needs_building)
                      else ()
              val status = if needs_building then Pending{needed=false}
                           else Succeeded
              val tgt_mtime = if is_phony then NONE
                              else hm_target.tgt_modTime tgt
              fun commandNode (c, local_depnodes, seqnum) =
                  {target = tgt, seqnum = seqnum,
                   status = status, phony = is_phony,
                   command = SomeCmd c, extra = extra,
                   dir = rh, mtime = tgt_mtime,
                   local_parallelism_limit = limit_for_dir rh,
                   dependencies = local_depnodes @ depnodes }
              fun foldthis (c, (depnodes, seqnum, g)) =
                let
                  val (g',n) = add_node (commandNode (c, depnodes, seqnum)) g
                in
                  (* This function needs to be folded l-to-r to ensure that
                     the last node is the one that gets recorded in the target
                     map, ensuring that if targets are marked as needed, the
                     earliest commands will get executed as dependencies of
                     the later commands *)
                  ([(n,tgt)], seqnum + 1, g')
                end
            in
              if needs_building then
                let
                  val (pfx, lastc) = front_last commands
                  val (lastnodelist, seqnum, g) = List.foldl foldthis ([], 0, g1) pfx
                  val lastInfo = commandNode (lastc, lastnodelist, seqnum)
                in
                  (lastInfo, g)
                end
              else
                case starred_dep of
                    NONE =>
                    ({target = tgt, seqnum = 0, phony = is_phony,
                      status = status, command = NoCmd, extra = extra,
                      dir = rh,
                      mtime = tgt_mtime,
                      local_parallelism_limit = limit_for_dir rh,
                      dependencies = depnodes}, g1)
                  | SOME s =>
                    let
                      val updstatus =
                          if needs_building_by_deps_existence then
                            Pending{needed=false}
                          else Succeeded
                      val fp = OS.Path.concat (hmdir.toAbsPath actual_dir, s)
                    in
                      ({target = tgt, seqnum = 0,
                        phony = false, status = updstatus,
                        command = BuiltInCmd (BIC_BuildScript fp, incinfo),
                        dir = actual_dir, extra = extra,
                        mtime = hm_target.tgt_modTime tgt,
                        local_parallelism_limit =
                        limit_for_dir actual_dir,
                        dependencies = depnodes}, g1)
                    end
            end
in
  case target_node g0 tgt of
      (x as SOME node) =>
      let
        val nInfo = valOf (peeknode g0 node) handle Option =>
                    raise Fail "depgraph build: invariant failure"
      in
        case #command nInfo of
            NoCmd => if hmdir.eqdir (#dir nInfo) actual_dir then
                       let
                         val _ = diag (fn _ => "Update NoCmd node for " ^
                                               hm_target.toString tgt)
                         val (nInfo', g) = buildNodeInfo g0
                       in
                         (updnode_fully (node, nInfo') g, node)
                       end
                     else (g0, node)
          | _ => (g0, node)
      end
    | NONE =>
      if not (hmdir.eqdir dir actual_dir) andalso
         no_extra_rule (SOME tgt) andalso
         not (isSome (pattern_rule_info tgt))
         (* path outside of current directory and no local rule (pattern or otherwise)
            claims it *)
      then (
        diag (fn _ => hm_target.toString tgt ^ " appears foreign; adding placeholdir NoCmd");
        add_node {target = tgt, seqnum = 0, phony = false,
                  status = if exists_readable fullpath_s then Succeeded
                           else Failed{needed=false},
                  dir = dir, extra = extra,
                  mtime = hm_target.tgt_modTime tgt,
                  local_parallelism_limit = limit_for_dir dir,
                  command = NoCmd, dependencies = []} g0
      ) else
        let val (nInfo, g) = buildNodeInfo g0
        in
          add_node nInfo g
        end
end

(* called in dir *)
fun get_targets dir =
    let
      val from_directory =
          deplist_to_set (generate_all_plausible_targets warn NONE)
      val (_, rules, _, _) = get_hmf()
    in
      Binarymap.foldl (fn (dep,v,acc) =>
                          if hm_target.filepart dep <> Unhandled ".PHONY" then
                            set_add dep acc
                          else acc)
                      from_directory
                      rules
    end

fun extend_graph_in_dir incinfo warn dir graph =
    let
      open HM_DepGraph
      val _ = diag "builddepgraph" (fn _ =>
                       "Extending graph in directory " ^ hmdir.pretty_dir dir)
      val dir_targets = get_targets dir
    in
      Binaryset.foldl
        (fn (t,g) => #1 (build_depgraph empty_cdset incinfo t g))
        graph
        dir_targets
    end

fun create_complete_graph cline_incs idm =
    let
      val d = hmdir.curdir()
      val {data = g, incdirmap, visited, ...} =
          recursively getnewincs (SOME cline_incs) {
            outputfns = scan_output_functions, verb = "Scanning",
            hm=extend_graph_in_dir,
            dirinfo={incdirmap=idm, visited = Binaryset.empty hmdir.compare,
                     ancestors = [original_dir]},
            dir = d,
            data = HM_DepGraph.empty()
          }
      val numScanned = Binaryset.numItems visited
      val _ = if numScanned > 1 then
                (#info_inline scan_output_functions
                              ("Scanned " ^ Int.toString numScanned ^
                               " directories");
                 #info_inline_end scan_output_functions())
              else ()
      val diag = diag "builddepgraph"
    in
      diag (fn _ => "Finished building complete dep graph (has " ^
                    Int.toString (HM_DepGraph.size g) ^ " nodes)");
      (g,idm_lookup incdirmap d)
    end

fun clean_deps() =
  ( Holmake_tools.clean_depdir {depdirname = DEPDIR}
  ; Holmake_tools.clean_depdir {depdirname = LOGDIR} )

fun do_clean_target x = let
  fun clean_action () =
      Holmake_tools.clean_dir outputfns {extra_cleans = extra_cleans()}
  fun cleanAll () =
      Holmake_tools.clean_dir outputfns {extra_cleans = extra_cleans() @ [".hol/"]}
in
  if originally_in_src orelse not (in_src()) then
    case x of
        "clean" => clean_action()
      | "cleanDeps" => ignore (clean_deps())
      | "cleanAll" => cleanAll()
    | _ => die ("Bad clean target " ^ x)
  else ()
end

val _ = not cline_always_rebuild_deps orelse clean_deps()

(* Top-level cline_incs gets the user's -I flags plus, when project
   mode is active, every project dir + external_include (minus
   original_dir itself so we don't trip recursively's cycle check on
   our own pre-visited cwd).  cline_incs is unioned into the top dir's
   recur_into at the start of `recursively`, which then walks each in
   classical post-order: project dirs and externals get their `hm`
   callbacks before cwd's, so their graph nodes are populated before
   cwd's compile dispatch references them. *)
val cwd_abs_canon = OS.Path.mkCanonical (hmdir.toAbsPath original_dir)
val project_incs_dirs =
    List.filter (fn d => OS.Path.mkCanonical d <> cwd_abs_canon)
                project_active_dirs
val cline_incs =
    Binaryset.union (slist_to_dset original_dir cline_additional_includes,
                     slist_to_dset original_dir project_incs_dirs)
val idmap0 = extend_idmap original_dir
                    {pres = empty_dirset, incs = empty_dirset}
                    empty_incdirmap

fun toplevel_build_graph () = create_complete_graph cline_incs idmap0

(* Behind the --dirs flag and "project mode".

   Threading each root through `recursively` with its own ancestors =
   [root] is what stops cross-root INCLUDES references from looking
   like cycles; genuine cycles inside one root's chain are still
   flagged.

   The shared `visited` set is what keeps each directory's
   contribution to the unified graph single-shot.

   dirmode_roots is the set of roots that should be used to generate actual build
   targets (in dirmode, this will be the set of directories the user has given on the
   command-line), otherwise it will be the current working directory.
*)
fun create_complete_graph_for_roots roots dirmode_roots idm =
    let
      val empty_visited = Binaryset.empty hmdir.compare
      fun for_root (root:hmdir.t, {graph, incdirmap, visited, must_build}) =
          let
            fun in_root () =
                let
                  val (_, _, _, target1) = get_hmf()
                  val root_targets =
                      if Binaryset.member(dirmode_roots, root) then
                        generate_all_plausible_targets warn target1
                      else []
                  val all_must_build = root_targets @ must_build
                in
                  if Binaryset.member(visited, root) then
                    {graph = graph, incdirmap = incdirmap, visited = visited,
                     must_build = all_must_build}
                  else
                    let
                      val {data = g', incdirmap = im', visited = v', ...} =
                          recursively getnewincs (SOME cline_incs) {
                            outputfns = scan_output_functions,
                            verb = "Scanning",
                            hm = extend_graph_in_dir,
                            dirinfo = {incdirmap = incdirmap,
                                       visited = visited,
                                       ancestors = if project_modep then [] else [root]},
                            dir = root,
                            data = graph
                          }
                    in
                      {graph = g', incdirmap = im', visited = v',
                       must_build = all_must_build}
                    end
                end
          in
            pushdir (hmdir.toAbsPath root) in_root ()
          end
      val {graph, visited, must_build, ...} =
          List.foldl for_root
                     {graph = HM_DepGraph.empty(),
                      incdirmap = idm, visited = empty_visited,
                      must_build = []}
                     roots
      val numScanned = Binaryset.numItems visited
      val _ = if numScanned > 1 then
                (#info_inline scan_output_functions
                              ("Scanned " ^ Int.toString numScanned ^
                               " directories");
                 #info_inline_end scan_output_functions ())
              else ()
      val diag = diag "builddepgraph"
    in
      diag (fn _ => "Finished building complete dep graph (has " ^
                    Int.toString (HM_DepGraph.size graph) ^ " nodes)");
      (graph, must_build)
    end

fun get_targets_recursively {incs, pres} =
    let
      val dirs = set_add original_dir (set_union incs pres)
      fun indir() =
          let val (_, _, _, target1) = get_hmf()
          in
            generate_all_plausible_targets warn target1
          end
    in
      List.concat (
        Binaryset.foldl
          (fn (d,A) => pushdir (hmdir.toAbsPath d) indir () :: A) [] dirs
      )
    end

fun check_targets_are_in_graph graph tgts =
    let
      fun check1 tgt =
          case target_node graph tgt of
              SOME _ => true
            | NONE => hm_target.tgtexists_readable tgt orelse
                      (warn ("Don't know how to build `" ^
                             hm_target.toString tgt ^ "'.");
                       false)
    in
      List.all check1 tgts orelse OS.Process.exit OS.Process.failure
    end

fun diag_built_graph targets depgraph =
    (diag "core" (
        fn _ =>
           let
             fun pr t = if hm_target.tgtexists_readable t then
                          tgt_toString t
                        else tgt_toString t ^ "(*)"
           in
             "Generated targets are: [" ^ concatWithf pr ", " targets ^ "]"
           end
      );
     diag "core" (fn _ => "Dep.graph =\n" ^ HM_DepGraph.toString depgraph))

fun dispatch_built_graph depgraph =
    if cline_nobuild then
      let val _ = print ("Dependency graph" ^
                         HM_DepGraph.toString depgraph ^
                         "\n\nTop-sorted:\n")
          val sorted = HM_DepGraph.topo_sort depgraph
          fun pr n =
              case HM_DepGraph.peeknode depgraph n of
                  NONE => die ("No node " ^ HM_DepGraph.node_toString n)
                | SOME nI =>
                  case #status nI of
                      Pending {needed = true} =>
                      print (hmdir.pretty_dir (#dir nI) ^ " - " ^
                             hm_target.toString (#target nI) ^ "\n")
                    | _ => ()
      in
        app pr sorted;
        OS.Process.success
      end
    else if show_json then (
      info (HM_DepGraph.toJSONString depgraph);
      OS.Process.exit OS.Process.success
    ) else
      postmortem finish_logging outputfns (build_graph depgraph)
      handle e => die ("Exception: " ^ General.exnMessage e)

fun hm_extend s = hmdir.extendp {base = original_dir, extension = s}
fun dirs_work () =
    let
      val _ = case targets of
                  [] => die "--dirs given but no root directories supplied"
                | _ => ()
      val hmd_targets = map hm_extend targets
      val roots = hmd_targets @ map hm_extend project_active_dirs
      val _ =
          List.app
              (fn r =>
                  let val p = hmdir.toAbsPath r
                  in
                    if FileSys.access (p, [FileSys.A_READ, FileSys.A_EXEC])
                       andalso FileSys.isDir p
                    then ()
                    else die ("--dirs: " ^ hmdir.pretty_dir r ^
                              " is not a readable directory")
                  end)
              roots
      val (depgraph, must_build) =
          create_complete_graph_for_roots
            roots
            (Binaryset.addList(Binaryset.empty hmdir.compare, hmd_targets))
            idmap0
      val depgraph =
          if toplevel_no_prereqs then
            mk_dirneeded (hmdir.curdir()) (mkneeded must_build depgraph)
          else
            mkneeded must_build depgraph
    in
      diag_built_graph must_build depgraph;
      dispatch_built_graph depgraph
    end

(* turns a c/line target name, probably a file like thing, but could also be "all" etc,
   into a dep *)
fun resolve_tgtname depgraph diep n =
    let val {dir,file} = OS.Path.splitDirFile n
        val cdir = hmdir.curdir()
        open hm_target
        fun maybe_die s = if diep then die s else NONE
    in
      if dir <> "" then SOME (filestr_to_tgt n)
      else
        let
          fun foldthis (_, ni) A =
              let val tgt = #target ni
              in
                if fromFile (filepart tgt) = n then tgt :: A else A
              end
          val candidates = HM_DepGraph.fold foldthis depgraph []
        in
          case candidates of
              [] =>
              if isSome (OS.Path.ext n) then
                maybe_die ("Can't make sense of target " ^ n)
              else
                (case resolve_tgtname depgraph false (n ^ ".uo") of
                     NONE => die ("Can't make sense of target " ^ n)
                   | SOME c => SOME c)
            | [c] => SOME c
            | cs =>
              case List.find (hmdir.eqdir cdir o dirpart) candidates
               of
                  SOME t => SOME t
                | NONE =>
                  maybe_die
                    ("Target " ^ n ^ " ambiguous; " ^
                     "could be from any of the following " ^
                     "directories: " ^
                     String.concatWith ", "
                                       (map (hmdir.toString o dirpart) cs))
        end
    end

fun projects_work () =
    let
      (* there is no --dirs flag, so targets are derived from cwd's
         Holmakefile, or c/line *)
      val (depgraph0, default_must_build) =
          create_complete_graph_for_roots
            (map hm_extend project_active_dirs)
            (Binaryset.singleton hmdir.compare (hmdir.curdir()))
            idmap0
      val real_targets =
          case targets of
              [] => default_must_build
            | _ => List.mapPartial (resolve_tgtname depgraph0 true) targets
      val depgraph =
          if toplevel_no_prereqs then
            mk_dirneeded (hmdir.curdir()) (mkneeded real_targets depgraph0)
          else
            mkneeded real_targets depgraph0
    in
      diag_built_graph real_targets depgraph;
      dispatch_built_graph depgraph
    end

val cleanTargets =
    List.filter (fn x => member x clean_target_strings) targets

fun clean_work() =
    let
      fun visit_and_clean tgts d =
          let
            val _ = FileSys.chDir (hmdir.toAbsPath d)
          in
            List.app do_clean_target tgts;
            FileSys.chDir (hmdir.toAbsPath original_dir)
          end
    in
      if cline_dirs then
        die ("--dirs does not accept clean targets " ^
             "(found: " ^ String.concatWith " " cleanTargets ^ ")")
      else if not cline_recursive_clean then
        (List.app (ignore o do_clean_target) cleanTargets;
         finish_logging true;
         OS.Process.success)
      else (
        recursively getnewincs (SOME cline_incs) {
          outputfns = outputfns, verb = "Cleaning",
          hm = (fn _ => fn _ => fn _ => fn _ =>
                   List.app (ignore o do_clean_target) cleanTargets),
          dirinfo = {incdirmap=idmap0, ancestors = [original_dir],
                     visited = Binaryset.empty hmdir.compare},
          dir = original_dir,
          data = ()
        };
        OS.Process.success
      )
    end


fun work() =
  if not (null cleanTargets) then clean_work()
  else if cline_dirs then dirs_work ()
  else if project_modep then projects_work()
  else
    case targets of
      [] => let
        val (depgraph, local_incinfo) = toplevel_build_graph()
        val targets = if cline_recursive_build then
                        get_targets_recursively local_incinfo
                      else generate_all_plausible_targets warn start_tgt
        val depgraph =
            if toplevel_no_prereqs then
              mk_dirneeded (hmdir.curdir()) (mkneeded targets depgraph)
            else
              mkneeded targets depgraph
      in
        diag_built_graph targets depgraph;
        dispatch_built_graph depgraph
      end
    | xs =>
      let
        val (depgraph, local_incinfo) = toplevel_build_graph()
        val targets = List.mapPartial (resolve_tgtname depgraph true) xs
        val depgraph =
            if toplevel_no_prereqs then
              mk_dirneeded (hmdir.curdir()) (mkneeded targets depgraph)
            else
              mkneeded targets depgraph
        val _ = check_targets_are_in_graph depgraph targets
      in
        if cline_nobuild then
          (print ("Dependency graph" ^ HM_DepGraph.toString depgraph);
           OS.Process.success)
        else
          postmortem finish_logging outputfns (build_graph depgraph)
          handle e => die ("Exception: "^General.exnMessage e)
      end

fun do_cachekey thyname =
    let
      val dat_tgt = filestr_to_tgt (thyname ^ ".dat")
      val (depgraph, _) = toplevel_build_graph()
      val node =
          case HM_DepGraph.target_node depgraph dat_tgt of
              SOME n => n
            | NONE =>
              die ("--cachekey: don't know how to build " ^
                   tgt_toString dat_tgt)
      val nodeinfo =
          case HM_DepGraph.peeknode depgraph node of
              SOME ni => ni
            | NONE => die "--cachekey: internal error (node not found)"
      val _ =
          case #command nodeinfo of
              HM_DepGraph.BuiltInCmd (HM_DepGraph.BIC_BuildScript _, _) => ()
            | _ => die ("--cachekey: " ^ thyname ^ " is not a theory target")
    in
      case #1 (HM_Cachekey.compute_for_node depgraph node) of
          HM_Cachekey.Key k => (print (k ^ "\n"); OS.Process.success)
        | HM_Cachekey.Missing ms =>
          let val first = hd ms
          in
            die ("--cachekey: dependency " ^ #name first ^
                 " (" ^ #path first ^ ") does not exist")
          end
    end

in
  if show_usage then
    print (GetOpt.usageInfo {
              header = "Usage:\n  " ^ CommandLine.name() ^ " [targets]\n\n\
                       \Special targets are: clean, cleanDeps and cleanAll\n\n\
                       \Extra options:",
              options = HM_Cline.option_descriptions
          })
  else case cline_cachekey of
      SOME thyname => let
        open Process
        val result = do_cachekey thyname
            handle internal_functions.HolmakeError s => die_raw s
                 | Fail s => die ("Fail exception: "^s^"\n")
      in
        exit result
      end
    | NONE => let
      open Process
      val result = work()
          handle internal_functions.HolmakeError s => die_raw s
               | Fail s => die ("Fail exception: "^s^"\n")
    in
      exit result
    end

end (* main *)

end (* struct *)
