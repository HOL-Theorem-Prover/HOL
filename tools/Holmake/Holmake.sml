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

fun slist_to_set slist =
    Binaryset.addList(Binaryset.empty String.compare, slist)
fun flist_to_set flist =
    Binaryset.addList(Binaryset.empty file_compare, flist)
fun slist_to_dset basedir slist =
    List.foldl
      (fn (s,dset) =>
          Binaryset.add(dset, hmdir.extendp {base=basedir, extension=s}))
      (Binaryset.empty hmdir.compare) slist

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

local
  val sigobj = OS.Path.concat(HOLDIR0, "sigobj")
  val frakS = String.implode (map Char.chr [0xF0,0x9D,0x94,0x96])
in
fun ppath s = if String.isPrefix sigobj s then
                frakS ^ String.extract(s,size sigobj,NONE)
              else s
fun pflist fs = String.concatWith ", " (map (ppath o fromFile) fs)
end


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

val master_cline_nohmf =
    HM_Cline.default_options |> apply_updates master_cline_options

fun read_holpathdb() =
    let
      val holpathdb_extensions =
          holpathdb.search_for_extensions (fn s => []) [OS.FileSys.getDir()]
      val _ = List.app holpathdb.extend_db holpathdb_extensions
      open Holmake_types
      fun foldthis ({vname,path}, env) = env_extend (vname, [LIT path]) env
    in
      List.foldl foldthis
                 (HM_BaseEnv.make_base_env master_cline_nohmf)
                 holpathdb_extensions
    end

local
  val base = read_holpathdb()
  val hmcache = ref (Binarymap.mkDict String.compare)
  val default = (base,Holmake_types.empty_ruledb,NONE)
  fun get_hmf0 d =
      if OS.FileSys.access("Holmakefile", [OS.FileSys.A_READ]) then
        ReadHMF.read "Holmakefile" (read_holpathdb())
        handle Fail s =>
               (warn ("Bad Holmakefile in " ^ d ^ ": " ^ s); default)
      else
        default
in
fun get_hmf () =
    let
      val d = OS.FileSys.getDir()
    in
      case Binarymap.peek(!hmcache, d) of
          NONE => let val result = get_hmf0 d
                  in
                    hmcache := Binarymap.insert (!hmcache, d, result);
                    result
                  end
        | SOME r => r
    end
end

fun getnewincs dir =
    let val (env, _, _) = get_hmf()
    in
      {includes = envlist env "INCLUDES" |> slist_to_dset dir,
       preincludes = envlist env "PREINCLUDES" |> slist_to_dset dir}
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
    val hmf_cline = envlist hmenv "CLINE_OPTIONS"
    val (hmf_options, hmf_rest) = getcline hmf_cline
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

val (start_hmenv, start_rules, start_tgt) = get_hmf()
val start_envlist = envlist start_hmenv
val start_options = start_envlist "OPTIONS"


fun chattiness_level switches =
  case (#debug switches, #verbose switches, #quiet switches) of
      (true, _, _) => 3
    | (_, true, _) => 2
    | (_, _, true) => 0
    | _ => 1

val option_value =
    HM_Cline.default_options
      |> apply_updates (get_hmf_cline_updates start_hmenv)
      |> apply_updates master_cline_options
val coption_value = #core option_value
val cmdl_HOLDIR = #holdir coption_value
val HOLDIR    = case cmdl_HOLDIR of NONE => HOLDIR0 | SOME s => s
val SIGOBJ    = normPath(Path.concat(HOLDIR, "sigobj"));


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
val quit_on_failure = #quit_on_failure coption_value
val toplevel_no_prereqs = #no_prereqs coption_value
val toplevel_no_overlay = #no_overlay coption_value
val cline_additional_includes = #includes coption_value
val cline_always_rebuild_deps = #rebuild_deps coption_value
val cline_nobuild = #no_action coption_value
val cline_recursive = #recursive coption_value

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
  "{" ^
  String.concatWith
    ", "
    (Binaryset.foldr (fn (d,acc) => hmdir.pretty_dir d :: acc) [] ds) ^
  "}"

type incmap = (hmdir.t, {incs:dirset,pres:dirset}) Binarymap.dict
type dirinfo = {incdirmap : incmap, visited : hmdir.t Binaryset.set}
type 'a hmfold =
     {includes : string list, preincludes : string list} ->
     (string -> unit) ->
     hmdir.t ->
     'a -> 'a
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
fun recursively getnewincs {warn,diag,hm : 'a hmfold,dirinfo,dir,data} =
let
  val {incdirmap,visited} = dirinfo : dirinfo
  val {includes=incset, preincludes = preincset} = getnewincs dir
  val incdirmap = extend_idmap dir {incs = incset, pres = preincset} incdirmap
  val recur_into = Binaryset.union(incset, preincset)
  fun recur_abbrev dir data (dirinfo:dirinfo) =
      recursively getnewincs {warn=warn,diag=diag,hm=hm,dirinfo=dirinfo,dir=dir,
                              data=data}
  val _ = diag (fn _ => "recursively: call in " ^ hmdir.pretty_dir dir)
  val _ = diag (fn _ => "recursively: includes (pre- & normal) = [" ^
                        String.concatWith ", "
                           (map hmdir.pretty_dir
                                (Binaryset.listItems recur_into)) ^ "]")
  val _ = diag (fn _ =>
                   "recursively: incdmap on dir " ^ hmdir.pretty_dir dir ^
                   " = " ^ print_set (#incs (idm_lookup incdirmap dir)))
  fun recurse (acc as {visited,incdirmap,data:'a}) newdir = let
  in
    if Binaryset.member(visited, newdir) then
      (* even if you don't want to rebuild newdir, you still want to learn
         about what it depends on so that the dependency map for this directory
         is appropriately augmented *)
      {visited = visited,
       data = data,
       incdirmap = extend_idmap dir (idm_lookup incdirmap newdir) incdirmap}
    else let
      val _ = OS.FileSys.access
                (hmdir.toAbsPath newdir, [OS.FileSys.A_READ, OS.FileSys.A_EXEC])
              orelse
                die ("Attempt to recurse into non-existent directory: " ^
                     hmdir.pretty_dir newdir ^
                     "\n  (Probably a result of bad INCLUDES spec.)")
      val _ = diag (fn _ => "recursively: Visited set = " ^ print_set visited)
      val _ = terminal_log ("Holmake: "^nice_dir (hmdir.toString newdir))
      val _ = OS.FileSys.chDir (hmdir.toAbsPath newdir)
      val result =
          case recur_abbrev newdir data {incdirmap=incdirmap, visited=visited}of
              {visited,incdirmap = idm0,data=data'} =>
              {visited = visited,
               incdirmap = extend_idmap dir (idm_lookup idm0 newdir) idm0,
               data = data'}
      val _ = OS.FileSys.chDir (hmdir.toAbsPath dir)
    in
      terminal_log ("Holmake: "^nice_dir (hmdir.toString dir));
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
            val data' = hm {includes=f incs,preincludes=f pres} warn dir data
          in
            {incdirmap = incdirmap, visited = visited, data = data'}
          end
        | x::xs => do_em (recurse accg x) xs
  val visited = Binaryset.add(visited, dir)
in
  do_em {visited = visited, incdirmap = incdirmap, data = data}
        (Binaryset.listItems recur_into) before
  diag (fn _ => "recursively: Finished work in "^hmdir.pretty_dir dir)
end

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

val actual_overlay = if toplevel_no_overlay then NONE else SOME DEFAULT_OVERLAY

val std_include_flags = [SIGOBJ]

fun local_rule_info t =
    let val (env, rules, _) = get_hmf()
    in
      Holmake_types.get_rule_info rules env t
    end

fun extra_deps t =
      Option.map #dependencies (local_rule_info t)

fun isPHONY t =
    case extra_deps ".PHONY" of
        NONE => false
      | SOME l => member t l

fun extra_commands t = Option.map #commands (local_rule_info t)

fun extra_targets() =
    let
      val (_, rules, _) = get_hmf()
    in
      Binarymap.foldr (fn (k,_,acc) => k::acc) [] rules
    end

fun extra_rule_for t = local_rule_info t
fun dir_varying_envlist s =
    let val (env, _, _) = get_hmf()
    in
      envlist env s
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
  diag (fn _ => "HOLDIR = "^HOLDIR);
  diag (fn _ => "Targets = [" ^ String.concatWith ", " targets ^ "]");
  diag (fn _ => "Additional includes = [" ^
                String.concatWith ", " cline_additional_includes ^ "]");
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
  val {preincludes,includes} = incinfo
  val file_dependencies0 =
      get_direct_dependencies {incinfo = incinfo,
                               extra_targets = extra_targets(),
                               output_functions = outputfns,
                               DEPDIR = DEPDIR} f
  val _ = diag (fn _ => "get_implicit_dependencies("^fromFile f^"), " ^
                        "directdeps = " ^ pflist file_dependencies0)
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
                                   extra_targets = extra_targets()}
      val starters = get_direct_dependencies f
      (* ignore theories as we don't want to depend on the script files
         behind them *)
      fun collect_all_dependencies sofar tovisit =
          case tovisit of
            [] => sofar
          | (UO (Theory _)::fs) => collect_all_dependencies sofar fs
          | (UI (Theory _)::fs) => collect_all_dependencies sofar fs
          | f::fs =>
            let
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
      val tcdeps = collect_all_dependencies starters starters
      val _ = diag (fn _ => "get_implicit_dependencies("^fromFile f^"), " ^
                            "tcdeps = " ^ pflist tcdeps)
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
    let
      val result = case (extra_deps (fromFile f)) of
                       SOME deps => map toFile deps
                     | NONE => []
    in
      diag (fn _ => fromFile f ^ " -explicitdeps-> " ^ pflist result);
      result
    end



(** Build graph *)

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

(* is run in a directory at a time *)
fun build_depgraph cdset incinfo target g0 : (t * node) = let
  val {preincludes,includes} = incinfo
  val incinfo = {preincludes = preincludes,
                 includes = std_include_flags @ includes}
  val pdep = primary_dependent target
  val target_s = fromFile target
  val dir = hmdir.curdir()
  fun addF f n = (n,fromFile f)
  fun nstatus g n = peeknode g n |> valOf |> #status
  fun build tgt' g =
    build_depgraph (Binaryset.add(cdset, target_s)) incinfo tgt' g
  val _ = not (Binaryset.member(cdset, target_s)) orelse
          die (target_s ^ " seems to depend on itself - failing")
in
  case target_node g0 (dir,target_s) of
      (x as SOME n) => (g0, n)
    | NONE =>
      if Path.dir target_s <> "" andalso
         Path.dir target_s <> "." andalso
         Path.dir target_s <> hmdir.toAbsPath dir andalso
         no_full_extra_rule target
         (* path outside of current directory *)
      then (
        diag (fn _ => "Target "^target_s^" external to directory");
        add_node {target = target_s, seqnum = 0, phony = false,
                  status = if exists_readable target_s then Succeeded
                           else Failed{needed=false},
                  dir = dir,
                  command = NoCmd, dependencies = []} g0
      )
      else if isSome pdep andalso no_full_extra_rule target then
        let
          val pdep = valOf pdep
          val (g1, pnode) = build pdep g0
          val _ = diag (fn _ => "Extended graph with primary dependency for " ^
                                target_s)
          val secondaries = set_union (get_implicit_dependencies incinfo target)
                                      (get_explicit_dependencies target)
          val _ = diag (fn _ => target_s ^ "-secondaries-> " ^
                                pflist secondaries)
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
                                         is_pending stat orelse is_failed stat
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
                      status = if needs_building then Pending{needed=false}
                               else Succeeded,
                      command = BuiltInCmd (bic,incinfo), dir = hmdir.curdir(),
                      dependencies = depnodes } g2
        end
      else
        case extra_rule_for target_s of
            NONE => (
              diag (fn _ => "No extra info/rule for target " ^ target_s);
              add_node {target = target_s, seqnum = 0, phony = false,
                        status = if exists_readable target_s then Succeeded
                                 else Failed{needed=false},
                        command = NoCmd, dir = hmdir.curdir(),
                        dependencies = []} g0
            )
          | SOME {dependencies, commands, ...} =>
            let
              val _ = diag (fn _ => "Extending graph with target " ^ target_s)
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
                  List.filter
                    (fn (n,_) => let val stat = nstatus g1 n
                                 in
                                   is_pending stat orelse is_failed stat
                                 end)
                    depnodes
              val is_phony = isPHONY target_s
              val _ = if is_phony then diag (fn _ => target_s ^" is phony")
                      else ()
              val needs_building_by_deps_existence =
                  not (OS.FileSys.access(target_s, [])) orelse
                  not (null unbuilt_deps) orelse
                  List.exists (fn d => d forces_update_of target_s)
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
                               if needs_building_by_deps_existence then
                                 Pending{needed=false}
                               else Succeeded
                         in
                           add_node {target = target_s, seqnum = 0,
                                     phony = false, status = updstatus,
                                     command = BuiltInCmd
                                                 (BIC_BuildScript s, incinfo),
                                     dir = dir,
                                     dependencies = depnodes} g1
                         end
                       | _ => die "Invariant failure in build_depgraph")
            end
end

(* called in dir *)
fun get_targets dir =
    let
      val from_directory =
          generate_all_plausible_targets warn NONE |> slist_to_set
      val (_, rules, _) = get_hmf()
    in
      Binarymap.foldl (fn (k,v,acc) => Binaryset.add(acc, k))
                      from_directory
                      rules
    end

val empty_tgts = Binaryset.empty String.compare
fun extend_graph_in_dir incinfo warn dir graph =
    let
      open HM_DepGraph
      val _ = diag (fn _ =>
                       "Extending graph in directory " ^ hmdir.pretty_dir dir)
      val dir_targets = get_targets dir
    in
      Binaryset.foldl
        (fn (t,g) => #1 (build_depgraph empty_tgts incinfo (toFile t) g))
        graph
        dir_targets
    end

fun create_complete_graph idm =
    let
      val d = hmdir.curdir()
      val {data = g, incdirmap,...} =
          recursively getnewincs {
            warn=warn,diag=diag,hm=extend_graph_in_dir,
            dirinfo={incdirmap=idm, visited = Binaryset.empty hmdir.compare},
            dir = d,
            data = HM_DepGraph.empty
          }
    in
      diag (fn _ => "Finished building complete dep graph (has " ^
                    Int.toString (HM_DepGraph.size g) ^ " nodes)");
      diag (fn _ => ("Graph is:\n"^ HM_DepGraph.toString g));
      (g,idm_lookup incdirmap d)
    end

fun clean_deps() =
  ( Holmake_tools.clean_depdir {depdirname = DEPDIR}
  ; Holmake_tools.clean_depdir {depdirname = LOGDIR} )

fun do_clean_target x = let
  fun clean_action () =
      Holmake_tools.clean_dir {extra_cleans = extra_cleans()}
in
  case x of
      "clean" => (info "Cleaning directory of object files\n"; clean_action())
    | "cleanDeps" => ignore (clean_deps())
    | "cleanAll" => (clean_action(); ignore (clean_deps()))
    | _ => die ("Bad clean target " ^ x)
end

val _ = not cline_always_rebuild_deps orelse clean_deps()

val (depgraph, local_incinfo) =
    create_complete_graph
      (extend_idmap original_dir {
          pres = empty_dirset,
          incs = slist_to_dset original_dir cline_additional_includes
        } empty_incdirmap)

fun work() =
  if cline_nobuild then
    (print ("Dependency graph:\n" ^ HM_DepGraph.toString depgraph);
     OS.Process.success)
  else
    case targets of
      [] => let
        val targets = generate_all_plausible_targets warn start_tgt
        val dir = hmdir.curdir()
        val targets = map (fn s => (dir, s)) targets
        val depgraph =
            if cline_recursive then make_all_needed depgraph
            else if toplevel_no_prereqs then mk_dirneeded dir depgraph
            else mkneeded targets depgraph
        val _ = diag (
              fn _ =>
                 let
                   val tgtstrings =
                       map
                         (fn (d,s) => if OS.FileSys.access(s, []) then s
                                      else s ^ "(*)")
                         targets
                 in
                   "Generated targets are: [" ^
                   String.concatWith ", " tgtstrings ^ "]"
                 end
            )
        val _ = diag (fn _ => "Dep.graph =\n" ^ HM_DepGraph.toString depgraph)
      in
        postmortem outputfns (build_graph depgraph)
      end
    | xs => let
        val cleanTargets =
            List.filter (fn x => member x ["clean", "cleanDeps", "cleanAll"]) xs
        fun visit_and_clean tgts d =
            let
              val _ = OS.FileSys.chDir (hmdir.toAbsPath d)
            in
              List.app do_clean_target tgts;
              OS.FileSys.chDir (hmdir.toAbsPath original_dir)
            end
        fun transform_thy_target s =
            if String.isSuffix "Theory" s then s ^ ".dat"
            else s
        val xs = map transform_thy_target xs
      in
        if not (null cleanTargets) then
          if not cline_recursive then
            (List.app (ignore o do_clean_target) cleanTargets;
             finish_logging true;
             OS.Process.success)
          else (
            Binaryset.app (visit_and_clean cleanTargets)
                          (Binaryset.add(Binaryset.union(#pres local_incinfo,
                                                         #incs local_incinfo),
                                         original_dir));
            OS.Process.success
          )
        else
          let
            val targets = map (fn s => (original_dir,s)) xs
          in
            postmortem outputfns (build_graph (mkneeded targets depgraph))
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
  else let
      open Process
      val result = work()
          handle Fail s => die ("Fail exception: "^s^"\n")
    in
      exit result
    end

end (* main *)

end (* struct *)

(** Local variable rubbish *)
(* local variables: *)
(* mode: sml *)
(* outline-regexp: " *(\\*\\*+" *)
(* end: *)
