structure buildcline_dtype =
struct

type t = {kernelspec : string option,
          help : bool,
          jobcount : int option,
          seqname : string option,
          build_theory_graph : bool option,
          selftest : int,
          relocbuild : bool}

val initial : t =
    { kernelspec = NONE, jobcount = NONE, seqname = NONE, help = false,
      build_theory_graph = NONE, selftest = 0,
      relocbuild = false
    }




end
