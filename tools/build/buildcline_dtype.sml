structure buildcline_dtype =
struct

type t = {kernelspec : string option,
          debug : bool,
          help : bool,
          keepgoing : bool,
          jobcount : int option,
          seqname : string option,
          multithread : int option,
          build_theory_graph : bool option,
          selftest : int option,
          relocbuild : bool,
          thmsrc : string option,
          timelimit : int option,
          cache_dir : string option}

val default_cache_dir =
    case (OS.Process.getEnv "XDG_CACHE_HOME", OS.Process.getEnv "HOME") of
        (SOME d, _) => SOME (OS.Path.concat(d, "HOL"))
      | (NONE, SOME h) => SOME (OS.Path.concat(OS.Path.concat(h, ".cache"), "HOL"))
      | (NONE, NONE) => NONE

(* cache_dir defaults to NONE: caching is opt-in via --use-cache (which
   the Holmake child sees and translates into cache_dir + cachekey
   rebuild strategy).  This field is essentially plumbing -- bin/build
   makes no decisions from it; the actual cache flag propagation is
   done by extract_cache_args on raw argv. *)
val initial : t =
    { kernelspec = NONE, jobcount = NONE, seqname = NONE, help = false,
      build_theory_graph = NONE, selftest = NONE, debug = false,
      relocbuild = false, multithread = NONE, keepgoing = false,
      thmsrc = NONE, timelimit = NONE,
      cache_dir = NONE
    }

type 'a final_options =
     {build_theory_graph : bool,
      cmdline : string list,
      debug : bool,
      selftest_level : int,
      extra : 'a,
      jobcount : int option,
      multithread : int option,
      keepgoing : bool,
      cache_dir : string option,
      relocbuild : bool,
      thmsrc : string option,
      timelimit : int option}




end
