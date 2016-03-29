structure HM_Core_Cline :> HM_Core_Cline =
struct

local
  open FunctionalRecordUpdate
  fun makeUpdateT z = makeUpdate19 z
in
fun updateT z = let
  fun from debug do_logging dontmakes fast help hmakefile holdir includes
           interactive keep_going no_hmakefile no_lastmaker_check no_overlay
           no_prereqs opentheory quiet
           quit_on_failure rebuild_deps recursive =
    {
      debug = debug, do_logging = do_logging, dontmakes = dontmakes,
      fast = fast, help = help, hmakefile = hmakefile, holdir = holdir,
      includes = includes, interactive = interactive, keep_going = keep_going,
      no_hmakefile = no_hmakefile,
      no_lastmaker_check = no_lastmaker_check, no_overlay = no_overlay,
      no_prereqs = no_prereqs, opentheory = opentheory,
      quiet = quiet, quit_on_failure = quit_on_failure,
      rebuild_deps = rebuild_deps, recursive = recursive
    }
  fun from' recursive rebuild_deps quit_on_failure quiet opentheory no_prereqs
            no_overlay no_lastmaker_check no_hmakefile keep_going interactive
            includes holdir
            hmakefile help fast dontmakes do_logging debug =
    {
      debug = debug, do_logging = do_logging, dontmakes = dontmakes,
      fast = fast, help = help, hmakefile = hmakefile, holdir = holdir,
      includes = includes, interactive = interactive, keep_going = keep_going,
      no_hmakefile = no_hmakefile,
      no_lastmaker_check = no_lastmaker_check, no_overlay = no_overlay,
      no_prereqs = no_prereqs, opentheory = opentheory,
      quiet = quiet, quit_on_failure = quit_on_failure,
      rebuild_deps = rebuild_deps, recursive = recursive
    }
  fun to f {debug, do_logging, dontmakes, fast, help, hmakefile, holdir,
            includes, interactive, keep_going, no_hmakefile, no_lastmaker_check,
            no_overlay, no_prereqs, opentheory,
            quiet, quit_on_failure, rebuild_deps, recursive} =
    f debug do_logging dontmakes fast help hmakefile holdir includes
      interactive keep_going no_hmakefile no_lastmaker_check no_overlay
      no_prereqs opentheory quiet
      quit_on_failure rebuild_deps recursive
in
  makeUpdateT (from, from', to)
end z
val U = U
val $$ = $$
end (* local *)

type t = {
  debug : bool,
  do_logging : bool,
  dontmakes : string list,
  fast : bool,
  help : bool,
  hmakefile : string option,
  holdir : string option,
  includes : string list,
  interactive : bool,
  keep_going : bool,
  no_hmakefile : bool,
  no_lastmaker_check : bool,
  no_overlay : bool,
  no_prereqs : bool,
  opentheory : string option,
  quiet : bool,
  quit_on_failure : bool,
  rebuild_deps : bool,
  recursive : bool
}

val default_core_options : t =
{
  debug = false,
  do_logging = false,
  dontmakes = [],
  fast = false,
  help = false,
  hmakefile = NONE,
  holdir = NONE,
  includes = [],
  interactive = false,
  keep_going = false,
  no_hmakefile = false,
  no_lastmaker_check = false,
  no_overlay = false,
  no_prereqs = false,
  opentheory = NONE,
  quiet = false,
  quit_on_failure = false,
  rebuild_deps = false,
  recursive = false
}

open GetOpt
fun mkBoolT sel = NoArg (fn () => fn (wn,t) => updateT t (U sel true) $$)
fun cons_dontmakes x (wn,t) = updateT t (U #dontmakes (x :: #dontmakes t)) $$
fun cons_includes x (wn,t) = updateT t (U #includes (x :: #includes t)) $$
fun set_hmakefile s (wn,t) =
  (if isSome (#hmakefile t) then
     wn "Multiple Holmakefile specs; ignoring earlier spec"
   else ();
   updateT t (U #hmakefile (SOME s)) $$)
fun set_holdir s (wn, t) =
  (if isSome (#holdir t) then
     wn "Multiple holdir specs; ignoring earlier spec"
   else ();
   updateT t (U #holdir (SOME s)) $$)
fun set_openthy s (wn, t) =
  (if isSome (#opentheory t) then
     wn "Multiple opentheory specs; ignoring earlier spec"
   else ();
   updateT t (U #opentheory (SOME s)) $$)
val core_option_descriptions = [
  { help = "turn on diagnostic messages", long = ["dbg", "d"], short = "",
    desc = mkBoolT #debug},
  { help = "don't make this target", long = [], short = "d",
    desc = ReqArg (cons_dontmakes, "target") },
  { help = "fast build (ignore tactic failure)", long = ["fast"], short = "",
    desc = mkBoolT #fast },
  { help = "show this message", long = ["help"], short = "h",
    desc = mkBoolT #help },
  { help = "use different HOLDIR", long = ["holdir"], short = "",
    desc = ReqArg (set_holdir, "directory") },
  { help = "use different holmakefile", long = ["holmakefile"], short = "",
    desc = ReqArg (set_hmakefile, "file") },
  { help = "make session 'interactive'", long = ["interactive"], short = "i",
    desc = mkBoolT #interactive },
  { help = "include directory", long = [], short = "I",
    desc = ReqArg (cons_includes, "directory") },
  { help = "try to build all targets", long = ["keep-going"], short = "k",
    desc = mkBoolT #keep_going },
  { help = "enable time logging", long = ["logging"], short = "",
    desc = mkBoolT #do_logging },
  { help = "don't use a Holmakefile", long = ["no_hmakefile"], short = "",
    desc = mkBoolT #no_hmakefile },
  { help = "don't check which Holmake was last used", long = ["nolmbc"],
    short = "", desc = mkBoolT #no_lastmaker_check },
  { help = "don't use Overlay.sml file", long = ["no_overlay"],
    short = "", desc = mkBoolT #no_overlay },
  { help = "don't build recursively in INCLUDES",
    long = ["no_prereqs"], short = "", desc = mkBoolT #no_prereqs },
  { help = "use file as opentheory logging .uo",
    long = ["ot"], short = "", desc = ReqArg (set_openthy, "file")},
  { help = "be quieter with output", short = "", long = ["quiet"],
    desc = mkBoolT #quiet },
  { help = "quit on failure", short = "", long = ["qof"],
    desc = mkBoolT #quit_on_failure },
  { help = "rebuild cached dependency files", short = "",
    long = ["rebuild_deps"], desc = mkBoolT #rebuild_deps },
  { help = "clean recursively", short = "r", long = [],
    desc = mkBoolT #recursive }
]



end
