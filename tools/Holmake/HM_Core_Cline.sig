signature HM_Core_Cline =
sig


type t = {
  debug : bool,
  do_logging : bool,
  dontmakes : string list,
  fast : bool,
  help : bool,
  holdir : string option,
  includes : string list,
  interactive : bool,
  jobs : int,
  keep_going : bool,
  no_action : bool,
  no_hmakefile : bool,
  no_lastmaker_check : bool,
  no_overlay : bool,
  no_prereqs : bool,
  opentheory : string option,
  quiet : bool,
  quit_on_failure : bool,
  rebuild_deps : bool,
  recursive : bool,
  hmakefile : string option
}

val default_core_options : t

val core_option_descriptions : ((string -> unit) * t -> t) GetOpt.opt_descr list

val sort_descriptions : 'a GetOpt.opt_descr list -> 'a GetOpt.opt_descr list

end
