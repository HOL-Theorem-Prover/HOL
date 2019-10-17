signature HM_Core_Cline =
sig

type t = {
  debug : string list option,
  do_logging : bool,
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
  hmakefile : string option,
  verbose : bool
}

val default_core_options : t
val fupd_jobs : (int -> int) -> (t -> t)
val fupd_includes : (string list -> string list) -> (t -> t)

type 'a cline_result =
     { update: (string -> unit) * 'a -> 'a, hmakefile : string option,
       no_hmf : bool }
val core_option_descriptions : t cline_result GetOpt.opt_descr list

val sort_descriptions : 'a GetOpt.opt_descr list -> 'a GetOpt.opt_descr list

end
