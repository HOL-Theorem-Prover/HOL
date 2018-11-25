(*---------------------------------------------------------------------------
     A special purpose version of make that "does the right thing" in
     single directories for building HOL theories, and accompanying
     SML libraries.
 ---------------------------------------------------------------------------*)

structure Holmake =
struct

open Systeml Holmake_tools Holmake_types
infix forces_update_of |>

fun x |> f = f x

structure FileSys = OS.FileSys
structure Path = OS.Path
structure Process = OS.Process

(* turn a variable name into a list *)
fun envlist env id = let
  open Holmake_types
in
  map dequote (tokenize (perform_substitution env [VREF id]))
end

fun main() = let

val execname = Path.file (CommandLine.name())
fun warn s = (TextIO.output(TextIO.stdErr, execname^": "^s^"\n");
              TextIO.flushOut TextIO.stdErr)
fun die s = (warn s; Process.exit Process.failure)
val original_dir = hmdir.curdir()

(* Global parameters, which get set at configuration time *)
val HOLDIR0 = Systeml.HOLDIR;
val DEPDIR = ".HOLMK";
val LOGDIR = ".hollogs";

(**** get_dependencies *)
(* figures out whether or not a dependency file is a suitable place to read
   information about current target or not, and then either does so, or makes
   the dependency file and then reads from it.

     f1 forces_update_of f2
     iff
     f1 exists /\ (f2 exists ==> f1 is newer than f2)
*)

(**** get dependencies from file *)



(** Command line parsing *)

(*** parse command line *)
fun apply_updates fs v = List.foldl (fn (f,v) => #update f (warn,v)) v fs

fun getcline args = let
  open GetOpt
in
  getOpt {argOrder = Permute,
          options = HM_Cline.option_descriptions,
          errFn = die}
         args
end

val (master_cline_options, targets) = getcline (CommandLine.arguments())

val (cline_hmakefile, cline_nohmf) =
    List.foldl (fn (f,(hmf,nohmf)) =>
                   ((case #hmakefile f of NONE => hmf | SOME s => SOME s),
                    nohmf orelse #no_hmf f))
               (NONE,false)
               master_cline_options

fun get_hmf_cline_updates () =
  let
    val hmakefile =
        case cline_hmakefile of
            NONE => "Holmakefile"
          | SOME s =>
            if exists_readable s then s
            else die ("Can't read holmakefile: "^s)
    val hmenv0 =
        if exists_readable hmakefile andalso not cline_nohmf then
          #1 (ReadHMF.read hmakefile (base_environment()))
        else
          base_environment()
    val hmf_cline = envlist hmenv0 "CLINE_OPTIONS"
    val (hmf_options, hmf_rest) = getcline hmf_cline
    val _ = if null hmf_rest then ()
            else
              warn ("Unused c/line options in makefile: "^
                    String.concatWith " " hmf_rest)
  in
    hmf_options
  end

fun chattiness_level switches =
  case (#debug switches, #verbose switches, #quiet switches) of
      (true, _, _) => 3
    | (_, true, _) => 2
    | (_, _, true) => 0
    | _ => 1

val option_value =
    HM_Cline.default_options |> apply_updates (get_hmf_cline_updates())
                             |> apply_updates master_cline_options
val coption_value = #core option_value
val usepfx =
  #jobs (#core
           (HM_Cline.default_options |> apply_updates master_cline_options)) =
  1

(* things that need to be read out of the first Holmakefile, and which will
   govern the behaviour even when recursing into other directories that may
   have their own Holmakefiles *)
val (outputfns as {warn,tgtfatal,diag,info,chatty}) =
    output_functions {chattiness = chattiness_level coption_value,
                      usepfx = usepfx}
val do_logging_flag = #do_logging coption_value
val no_lastmakercheck = #no_lastmaker_check coption_value
val show_usage = #help coption_value
val toplevel_no_prereqs = #no_prereqs coption_value
val cline_additional_includes = #includes coption_value

(* make the cline includes = [] so that these are only looked at once
   (when the cline_additional_includes value is folded into dirinfo values
   and eventually used in hm_recur).
*)
val pass_option_value =
    HM_Cline.fupd_core (HM_Core_Cline.fupd_includes (fn _ => [])) option_value

val _ = do_lastmade_checks outputfns {no_lastmakercheck = no_lastmakercheck}

val _ = diag (fn _ => "CommandLine.name() = "^CommandLine.name())
val _ = diag (fn _ => "CommandLine.arguments() = "^
                      String.concatWith ", " (CommandLine.arguments()))

(* set up logging *)
val logfilename = Systeml.make_log_file
val hostname = if Systeml.isUnix then
                 case Mosml.run "hostname" [] "" of
                   Mosml.Success s => String.substring(s,0,size s - 1) ^ "-"
                                      (* substring to drop \n in output *)
                 | _ => ""
               else "" (* what to do under windows? *)

fun finish_logging buildok = let
in
  if do_logging_flag andalso FileSys.access(logfilename, []) then let
      open Date
      val timestamp = fmt "%Y-%m-%dT%H%M" (fromTimeLocal (Time.now()))
      val newname0 = hostname^timestamp
      val newname = (if buildok then "" else "bad-") ^ newname0
    in
      FileSys.rename {old = logfilename, new = newname};
      buildok
    end
  else buildok
end handle IO.Io _ => (warn "Had problems making permanent record of make log";
                       buildok)

val _ = Process.atExit (fn () => ignore (finish_logging false))

(* ----------------------------------------------------------------------

    maybe_recurse

    this function doesn't handle all recursion, just one level's
    worth. In other words, the master Holmake calls this function, and
    this then arranges the recursive calls into the various include
    directories that need to happen. The holmake that gets called in
    those directories (via the hm parameter) will in turn call this
    function for recursion at that level in the "tree".

    The local_build/k parameter is how the maybe_recurse function
    finishes off; this parameter is called when all of the necessary
    recursion has been performed and work should be done in the
    current ("local") directory.

    Finally, what of the dirinfo?

    This record includes
          origin: the absolute path to the very first directory
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
  "{" ^
  String.concatWith
    ", "
    (Binaryset.foldr (fn (d,acc) => hmdir.toString d :: acc) [] ds) ^
  "}"

fun maybe_recurse {warn,diag,hm,dirinfo,dir,local_build=k,cleantgt} allincs =
let
  val {incdirmap,visited} = dirinfo
  val _ = diag (fn _ => "maybe_recurse: includes (pre- & normal) = [" ^
                        String.concatWith ", " allincs ^ "]")
  val _ = diag (fn _ =>
                   "maybe_recurse: incdmap on dir \"" ^ hmdir.toString dir ^
                   " = " ^ print_set (#incs (idm_lookup incdirmap dir)))
  val k = fn ii => (terminal_log ("Holmake: "^nice_dir (hmdir.toString dir));
                    k ii)
  val tgts = case cleantgt of SOME s => [s] | NONE => []
  fun recurse (acc as {visited,incdirmap}) newdir = let
  in
    if Binaryset.member(visited, newdir) then
      (* even if you don't want to rebuild newdir, you still want to learn
         about what it depends on so that the dependency map for this directory
         is appropriately augmented *)
      SOME {visited = visited,
            incdirmap =
              extend_idmap dir (idm_lookup incdirmap newdir) incdirmap}
    else let
      val _ = OS.FileSys.access
                (hmdir.toAbsPath newdir, [OS.FileSys.A_READ, OS.FileSys.A_EXEC])
              orelse
                die ("Attempt to recurse into non-existent directory: " ^
                     hmdir.toString newdir ^
                     "\n  (Probably a result of bad INCLUDES spec.)")
      val _ = diag (fn _ => "Recursive call in " ^ hmdir.pretty_dir newdir)
      val _ = diag (fn _ => "Visited set = " ^ print_set visited)
      val _ = terminal_log ("Holmake: "^nice_dir (hmdir.toString newdir))
      val result =
          case hm newdir acc tgts of
              NONE => NONE
            | SOME {visited,incdirmap = idm0} =>
              SOME {visited = visited,
                    incdirmap = extend_idmap dir (idm_lookup idm0 newdir) idm0}
    in
      diag (fn _ => "Finished work in "^hmdir.pretty_dir newdir);
      terminal_log ("Holmake: "^nice_dir (hmdir.toString dir));
      FileSys.chDir (hmdir.toAbsPath dir);
      case result of
          SOME{visited,incdirmap} =>
          let
            val {incs,pres} = idm_lookup incdirmap dir
          in
            diag (fn () =>
                     "Recursively computed includes for " ^ hmdir.toString dir ^
                     " = " ^ print_set incs);
            diag (fn () =>
                     "Recursively computed pre-includes for " ^
                     hmdir.toString dir ^
                     " = " ^ print_set pres)
          end
        | NONE => ();
      result
    end
  end
  fun do_em (accg as {incdirmap,...}) dirs =
      case dirs of
          [] =>
          let
            val {pres, incs} = idm_lookup incdirmap dir
            val f = Binaryset.foldr (fn (d,acc) => hmdir.toAbsPath d :: acc) []
          in
            if k {includes=f incs,preincludes=f pres} then SOME accg
            else NONE
          end
        | x::xs =>
          let
          in
            case recurse accg x of
                SOME result => do_em result xs
              | NONE => NONE
          end
  val visited = Binaryset.add(visited, dir)
  fun canon i = hmdir.extendp {base = dir, extension = i}
  val canonl = map canon
  fun f idirs = map canon idirs
in
  do_em {visited = visited, incdirmap = incdirmap} (hmdir.sort (f allincs))
end

(* directory specific stuff here *)
type res = holmake_result
fun Holmake nobuild dir dirinfo cline_additional_includes targets : res = let
  val _ = OS.FileSys.chDir (hmdir.toAbsPath dir)

  val option_value =
      pass_option_value |> apply_updates (get_hmf_cline_updates())
  val coption_value = #core option_value

  val allfast = #fast coption_value
  val always_rebuild_deps = #rebuild_deps coption_value
  val cline_recursive = #recursive coption_value
  val debug = #debug coption_value
  val dontmakes = #dontmakes coption_value
  val user_hmakefile = #hmakefile coption_value
  val cmdl_HOLDIR = #holdir coption_value
  val cline_additional_includes =
      cline_additional_includes @ #includes coption_value
  val keep_going_flag = #keep_going coption_value
  val no_action = #no_action coption_value
  val no_hmakefile = #no_hmakefile coption_value
  val no_overlay = #no_overlay coption_value
  val no_prereqs = #no_prereqs coption_value
  val opentheory = #opentheory coption_value
  val quiet_flag = #quiet coption_value
  val quit_on_failure = #quit_on_failure coption_value
  val verbose = #verbose coption_value
  (* find HOLDIR by first looking at command-line, then looking
     for a value compiled into the code.
  *)
  val HOLDIR    = case cmdl_HOLDIR of NONE => HOLDIR0 | SOME s => s
  val SIGOBJ    = normPath(Path.concat(HOLDIR, "sigobj"));


(* prepare to do logging *)
val () = if do_logging_flag then
           if FileSys.access (logfilename, []) then
             warn "Make log exists; new logging will concatenate on this file"
           else let
               (* touch the file *)
               val outs = TextIO.openOut logfilename
             in
               TextIO.closeOut outs
             end handle IO.Io _ => warn "Couldn't set up make log"
         else ()



val hmakefile =
  case user_hmakefile of
    NONE => "Holmakefile"
  | SOME s =>
      if exists_readable s then s
      else die_with ("Couldn't read/find makefile: "^s)

val base_env = HM_BaseEnv.make_base_env option_value

val (hmakefile_env, extra_rules, first_target) =
  if exists_readable hmakefile andalso not no_hmakefile
  then let
      val () = diag (fn _ => "Reading additional information from "^hmakefile)
    in
      ReadHMF.read hmakefile base_env
    end
  else (base_env, Holmake_types.empty_ruledb, NONE)

val envlist = envlist hmakefile_env

val hmake_includes = envlist "INCLUDES"
val hmake_options = envlist "OPTIONS"
val additional_includes =
  remove_duplicates (cline_additional_includes @ hmake_includes)

val hmake_preincludes = envlist "PRE_INCLUDES"
val hmake_no_overlay = member "NO_OVERLAY" hmake_options
val hmake_no_sigobj = member "NO_SIGOBJ" hmake_options
val hmake_qof = member "QUIT_ON_FAILURE" hmake_options
val hmake_noprereqs = member "NO_PREREQS" hmake_options
val extra_cleans = envlist "EXTRA_CLEANS"

val quit_on_failure = quit_on_failure orelse hmake_qof

val _ = if cline_recursive andalso no_prereqs then
          warn("-r forces recursion, taking precedence over --no_prereqs")
        else ()
val no_prereqs = (no_prereqs orelse hmake_noprereqs) andalso not cline_recursive

val _ =
  if quit_on_failure andalso allfast then
    warn "quit on (tactic) failure ignored for fast built theories"
  else
    ()

val no_sigobj = hmake_no_sigobj
val actual_overlay =
  if no_sigobj orelse no_overlay orelse hmake_no_overlay then NONE
  else SOME DEFAULT_OVERLAY

val std_include_flags = if no_sigobj then [] else [SIGOBJ]

fun extra_deps t =
    Option.map #dependencies
               (Holmake_types.get_rule_info extra_rules hmakefile_env t)

fun isPHONY t =
  case extra_deps ".PHONY" of
      NONE => false
    | SOME l => member t l

fun extra_commands t =
    Option.map #commands
               (Holmake_types.get_rule_info extra_rules hmakefile_env t)

val extra_targets = Binarymap.foldr (fn (k,_,acc) => k::acc) [] extra_rules

fun extra_rule_for t = Holmake_types.get_rule_info extra_rules hmakefile_env t

(* treat targets as sets *)
infix in_target
fun (s in_target t) = case extra_deps t of NONE => false | SOME l => member s l

(*** Compilation of files *)
val binfo : HM_Cline.t BuildCommand.buildinfo_t =
    {optv = option_value, hmake_options = hmake_options,
     actual_overlay = actual_overlay, envlist = envlist,
     hmenv = hmakefile_env,
     quit_on_failure = quit_on_failure, outs = outputfns,
     SIGOBJ = SIGOBJ}
val {extra_impl_deps,build_graph} = BuildCommand.make_build_command binfo

val _ = let
in
  diag (fn _ => "HOLDIR = "^HOLDIR);
  diag (fn _ => "Targets = [" ^ String.concatWith ", " targets ^ "]");
  diag (fn _ => "Additional includes = [" ^
                String.concatWith ", " additional_includes ^ "]");
  diag (fn _ => "Using HOL sigobj dir = "^Bool.toString (not no_sigobj));
  diag (fn _ => HM_BaseEnv.debug_info option_value)
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

fun get_implicit_dependencies incinfo (f: File) : File list = let
  val _ = diag (fn _ => "Calling get_implicit_dependencies on "^fromFile f)
  val file_dependencies0 =
      get_direct_dependencies {incinfo = incinfo, extra_targets = extra_targets,
                               output_functions = outputfns,
                               DEPDIR = DEPDIR} f
  val file_dependencies =
      case actual_overlay of
        NONE => file_dependencies0
      | SOME s => if isSome (holdep_arg f) then
                    toFile (fullPath [SIGOBJ, s]) :: file_dependencies0
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
                                   extra_targets = extra_targets}
      fun collect_all_dependencies sofar tovisit =
          case tovisit of
            [] => sofar
          | (f::fs) => let
              val deps =
                  if Path.dir (string_part f) <> "" then []
                  else
                    case f of
                      UI x => (get_direct_dependencies f @
                               get_direct_dependencies (UO x))
                    | _ => get_direct_dependencies f
              val newdeps = set_diff deps sofar
            in
              collect_all_dependencies (sofar @ newdeps)
                                       (set_union newdeps fs)
            end
      val tcdeps = collect_all_dependencies [] [f]
      val uo_deps =
          List.mapPartial (fn (UI x) => SOME (UO x) | _ => NONE) tcdeps
      val alldeps = set_union (set_union tcdeps uo_deps)
                              (set_union file_dependencies extra_impl_deps)
    in
      case f of
        SML x => let
          (* there may be theory files mentioned in the Theory.sml file that
             aren't mentioned in the script file.  If so, we are really
             dependent on these, and should add them.  They will be listed
             in the dependencies for UO (Theory x). *)
          val additional_theories =
              if exists_readable (fromFile f) then
                List.mapPartial
                  (fn (x as (UO (Theory s))) => SOME x | _ => NONE)
                  (get_implicit_dependencies incinfo (UO x))
              else []
        in
          set_union alldeps additional_theories
        end
      | _ => alldeps
    end
  else
    file_dependencies
end

fun get_explicit_dependencies (f : File) : File list =
    case (extra_deps (fromFile f)) of
      SOME deps => map toFile deps
    | NONE => []

(** Build graph *)

(*
fun do_a_build_command incinfo target pdep secondaries =
  case (extra_commands (fromFile target)) of
    SOME (cs as _ :: _) =>
      Process.isSuccess (run_extra_commands (fromFile target) cs secondaries)
  | _ (* i.e., NONE or SOME [] *) => let
      val build_command = build_command incinfo
    in
      case target of
         UO c           => build_command (Compile secondaries) pdep
       | UI c           => build_command (Compile secondaries) pdep
       | SML (Theory s) => build_command (BuildScript (s, secondaries)) pdep
       | SIG (Theory s) => build_command (BuildScript (s, secondaries)) pdep
       | ART (RawArticle s) => build_command (BuildArticle(s, secondaries)) pdep
       | ART (ProcessedArticle s) => build_command (ProcessArticle s) pdep
       | x => raise Fail "Can't happen"
                    (* can't happen because do_a_build_command is only
                       called on targets that have primary_dependents,
                       and those are those targets of the shapes already
                       matched in the previous cases *)
    end
*)

exception CircularDependency
exception BuildFailure
exception NotFound

fun no_full_extra_rule tgt =
    case extra_commands (fromFile tgt) of
      NONE => true
    | SOME cl => null cl

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

fun build_depgraph cdset incinfo target g0 : (t * node) = let
  val pdep = primary_dependent target
  val target_s = fromFile target
  fun addF f n = (n,fromFile f)
  fun nstatus g n = peeknode g n |> valOf |> #status
  fun build tgt' g =
    build_depgraph (Binaryset.add(cdset, target_s)) incinfo tgt' g
  val _ = not (Binaryset.member(cdset, target_s)) orelse
          die (target_s ^ " seems to depend on itself - failing")
in
  case target_node g0 target_s of
      (x as SOME n) => (g0, n)
    | NONE =>
      if Path.dir (string_part target) <> "" andalso
         Path.dir (string_part target) <> "." andalso
         no_full_extra_rule target
         (* path outside of current directory *)
      then
        add_node {target = target_s, seqnum = 0, phony = false,
                  status = if exists_readable target_s then Succeeded
                           else Failed,
                  dir = hmdir.curdir(),
                  command = NoCmd, dependencies = []} g0
      else if isSome pdep andalso no_full_extra_rule target then
        let
          val pdep = valOf pdep
          val (g1, pnode) = build pdep g0
          val secondaries = set_union (get_implicit_dependencies incinfo target)
                                      (get_explicit_dependencies target)
          fun foldthis (d, (g, secnodes)) =
            let
              val (g', n) = build d g
            in
              (g', addF d n::secnodes)
            end
          val (g2, depnodes : (HM_DepGraph.node * string) list) =
              List.foldl foldthis (g1, [addF pdep pnode]) secondaries
          val unbuilt_deps =
              List.filter (fn (n,_) => let val stat = nstatus g2 n
                                       in
                                         stat = Pending orelse stat = Failed
                                       end)
                          depnodes
          val needs_building =
              not (null unbuilt_deps) orelse
              List.exists (fn d => d forces_update_of target_s)
                          (fromFile pdep :: map fromFile secondaries)
          val bic = case toFile target_s of
                        SML (Theory s) => BIC_BuildScript s
                      | SIG (Theory s) => BIC_BuildScript s
                      | DAT s => BIC_BuildScript s
                      | _ => BIC_Compile
        in
            add_node {target = target_s, seqnum = 0, phony = false,
                      status = if needs_building then Pending else Succeeded,
                      command = BuiltInCmd bic, dir = hmdir.curdir(),
                      dependencies = depnodes } g2
        end
      else
        case extra_rule_for target_s of
            NONE =>
              add_node {target = target_s, seqnum = 0, phony = false,
                        status = if exists_readable target_s then Succeeded
                                 else Failed,
                        command = NoCmd, dir = hmdir.curdir(),
                        dependencies = []} g0
          | SOME {dependencies, commands, ...} =>
            let
              fun foldthis (d, (g, secnodes)) =
                let
                  val (g, n) = build d g
                in
                  (g, addF d n::secnodes)
                end
              fun depfoldthis (s, (starp, deps)) =
                if s <> "" andalso String.sub(s,0) = #"*" andalso
                   is_script s
                   (* is_script returns true for, e.g., *boolScript.sml *)
                then
                  if isSome starp then
                    die ("Multiple starred script dependencies for "^target_s)
                  else
                    let
                      val s = String.extract(s,1,NONE)
                    in
                      (SOME s, s :: deps)
                    end
                else (starp, s::deps)
              val (starred_dep, dependencies) =
                  if null commands then
                    List.foldr depfoldthis (NONE, []) dependencies
                  else (NONE, dependencies)

              val more_deps =
                  case starred_dep of
                      NONE => []
                    | SOME s =>
                        get_implicit_dependencies
                          incinfo
                          (SML(Theory (valOf (de_script s))))
                          handle Option => die "more_deps invariant failure"

              val (g1, depnodes) =
                  List.foldl foldthis (g0, [])
                             (more_deps @ map toFile dependencies)

              val unbuilt_deps =
                  List.filter (fn (n,_) => let val stat = nstatus g1 n
                                           in
                                             stat = Pending orelse stat = Failed
                                           end)
                              depnodes
              val is_phony = isPHONY target_s
              val needs_building_by_deps_existence =
                  (not (OS.FileSys.access(target_s, [])) orelse
                   not (null unbuilt_deps) orelse
                   List.exists (fn d => d forces_update_of target_s)
                               dependencies orelse
                   is_phony)
              val needs_building =
                  needs_building_by_deps_existence andalso
                  not (null commands)
              val status = if needs_building then Pending else Succeeded
              fun foldthis (c, (depnode, seqnum, g)) =
                let
                  val (g',n) = add_node {target = target_s, seqnum = seqnum,
                                         status = status, phony = is_phony,
                                         command = SomeCmd c,
                                         dir = hmdir.curdir(),
                                         dependencies = depnode @ depnodes } g
                in
                  (* The "" is necessary to make multi-command, multi-target
                     rules work: when subsequent nodes (seqnum > 0) are added
                     to the graph targetting a target other than the first,
                     it is important that this new node merges with the
                     corresponding seqnum>0 node generated from the first
                     target *)
                  ([(n,"")], seqnum + 1, g')
                end
            in
              if needs_building then
                let
                  val (lastnodelist, _, g) =
                      List.foldl foldthis ([], 0, g1) commands
                in
                  (g, #1 (hd lastnodelist))
                end
              else
                case starred_dep of
                    NONE =>
                    add_node {target = target_s, seqnum = 0, phony = is_phony,
                              status = status, command = NoCmd,
                              dir = hmdir.curdir(), dependencies = depnodes} g1
                  | SOME scr =>
                    (case toFile scr of
                         SML (Script s) =>
                         let
                           val updstatus =
                               if needs_building_by_deps_existence then Pending
                               else Succeeded
                         in
                           add_node {target = target_s, seqnum = 0,
                                     phony = false, status = updstatus,
                                     command = BuiltInCmd (BIC_BuildScript s),
                                     dir = hmdir.curdir(),
                                     dependencies = depnodes} g1
                         end
                       | _ => die "Invariant failure in build_depgraph")
            end
end


val allincludes =
    cline_additional_includes @ hmake_includes

fun add_sigobj {includes,preincludes} =
    {includes = std_include_flags @ includes,
     preincludes = preincludes}

fun null_ii {includes,preincludes} = null includes andalso null preincludes

val extended_dirinfo =
    let
      fun mkd s = hmdir.extendp{base = dir, extension = s}
      val mkS =
          List.foldl (fn (s, acc) => Binaryset.add(acc, mkd s)) empty_dirset
    in
      {
        visited = #visited dirinfo,
        incdirmap =
          extend_idmap
            dir
            {incs= mkS allincludes, pres= mkS hmake_preincludes}
            (#incdirmap dirinfo)
      }
    end

val recurse_into_dirs = allincludes @ hmake_preincludes

fun hm_recur ctgt k : holmake_result = let
  val nobuild = toplevel_no_prereqs orelse no_prereqs
  fun hm dir dirinfo targets =
      Holmake nobuild dir dirinfo [] targets
  val warn = if nobuild then (fn _ => ()) else warn
in
  maybe_recurse
      {warn = warn,
       diag = diag,
       hm = hm,
       dirinfo = extended_dirinfo,
       dir = dir,
       local_build = k,
       cleantgt = ctgt}
      recurse_into_dirs
end

fun create_graph tgts ii =
  let
    open HM_DepGraph
    val empty_tgts = Binaryset.empty String.compare
    val _ = diag(fn _ => "Building dep. graph with targets: " ^
                         String.concatWith " " tgts)
    val g =
        List.foldl
          (fn (t, g) => #1 (build_depgraph empty_tgts ii t g))
          empty
          (map toFile tgts)
  in
    diag (fn _ => "Finished building dep graph (has " ^
                  Int.toString (size g) ^ " nodes)");
    g
  end

fun clean_deps() =
  ( Holmake_tools.clean_depdir {depdirname = DEPDIR}
  ; Holmake_tools.clean_depdir {depdirname = LOGDIR} )

fun do_clean_target x = let
  fun clean_action () =
      (Holmake_tools.clean_dir {extra_cleans = extra_cleans}; true)
in
  case x of
      "clean" => ((info "Cleaning directory of object files\n";
                   clean_action();
                   true) handle _ => false)
    | "cleanDeps" => clean_deps()
    | "cleanAll" => clean_action() andalso clean_deps()
    | _ => die ("Bad clean target " ^ x)
end

fun basecont tgts ii =
  if List.exists (fn x => member x ["clean", "cleanDeps", "cleanAll"]) tgts then
    (app (ignore o do_clean_target) tgts; true)
  else
    let
      open HM_DepGraph
      val _ = if null_ii ii andalso hmdir.compare(dir,original_dir) = EQUAL then
                ()
              else warn (bold ("Working in " ^ hmdir.pretty_dir dir))
      val ii = add_sigobj ii
      val g = create_graph tgts ii
      val _ = diag (fn _ => "Building from graph")
      val res = build_graph ii g
      val buildok = OS.Process.isSuccess res
      val _ = diag (fn _ => "Built from graph with result " ^
                            (if buildok then "OK" else "FAILED"))
    in
      finish_logging buildok
    end

fun no_action_cont tgts ii =
  let
    open HM_DepGraph
    val ii = add_sigobj ii
    val g = create_graph tgts ii
    fun pr s = s
    fun str (n,ni) =
      "{" ^ node_toString n ^ "}: " ^ nodeInfo_toString pr ni ^ "\n"
  in
    List.app (print o str) (listNodes g);
    true
  end

val stdcont = if no_action then no_action_cont else basecont

val _ = not always_rebuild_deps orelse clean_deps()

in
  if nobuild then hm_recur NONE (fn _ => true)
  else
    case targets of
      [] => let
        val targets = generate_all_plausible_targets warn first_target
        val targets = map fromFile targets
        val _ =
            let
              val tgtstrings =
                  map
                    (fn s => if OS.FileSys.access(s, []) then s else s ^ "(*)")
                    targets
            in
              diag(fn _ => "Generated targets are: [" ^
                           String.concatWith ", " tgtstrings ^ "]")
            end
      in
        hm_recur NONE (stdcont targets)
      end
    | xs => let
        val cleanTarget_opt =
            List.find (fn x => member x ["clean", "cleanDeps", "cleanAll"]) xs
        fun canon i = hmdir.extendp {base = dir, extension = i}
      in
        if isSome cleanTarget_opt andalso not cline_recursive then
          (List.app (ignore o do_clean_target) xs;
           finish_logging true;
           SOME dirinfo)
        else
            hm_recur cleanTarget_opt (stdcont xs)
      end
end (* fun Holmake *)


in
  if show_usage then
    print (GetOpt.usageInfo {
              header = "Usage:\n  " ^ CommandLine.name() ^ " [targets]\n\n\
                       \Special targets are: clean, cleanDeps and cleanAll\n\n\
                       \Extra options:",
              options = HM_Cline.option_descriptions
          })
  else let
      open Process
      val result =
          Holmake false (* yes, build something *)
                  (hmdir.curdir())
                  {visited = Binaryset.empty hmdir.compare,
                   incdirmap = empty_incdirmap}
            cline_additional_includes
            targets
          handle Fail s => die ("Fail exception: "^s^"\n")
    in
      if isSome result then exit success
      else exit failure
    end

end (* main *)

end (* struct *)

(** Local variable rubbish *)
(* local variables: *)
(* mode: sml *)
(* outline-regexp: " *(\\*\\*+" *)
(* end: *)
