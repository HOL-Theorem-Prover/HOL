(* Copyright (c) 2010 Tjark Weber. All rights reserved. *)

structure QbfTrace =
struct

  (* possible values:
     0 - no output at all (except for fatal errors)
     1 - warnings only
     2 - also diagnostic messages of constant length
     3 - also diagnostic messages that are potentially lengthy (e.g., terms,
         models, proofs)
     4 - moreover, temporary files (for communication with the QBF solver) are
         not removed after solver invocation *)
  val {get = trace, flag = trace_flag, ...} =
      HOLFlags.create_trace ({group = "HolQbfLib", name = "trace"},
                             {initial = 2, max = 4})

end
