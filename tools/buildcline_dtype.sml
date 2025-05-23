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
          timelimit : int option}

val initial : t =
    { kernelspec = NONE, jobcount = NONE, seqname = NONE, help = false,
      build_theory_graph = NONE, selftest = NONE, debug = false,
      relocbuild = false, multithread = NONE, keepgoing = false,
      timelimit = NONE
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
      relocbuild : bool,
      timelimit : int option}




end
