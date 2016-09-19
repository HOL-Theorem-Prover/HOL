structure GrammarAncestry :> GrammarAncestry =
struct

open HolKernel

fun ERR f s = HOL_ERR {origin_structure = "GrammarAncestry",
                       origin_function = f, message = s}
val tag = "GrammarAncestry"

val (write, read) =
    Theory.LoadableThyData.new {thydataty = tag, merge = op @,
                                read = Lib.K Coding.StringData.decodel,
                                terms = Lib.K [],
                                write = Lib.K Coding.StringData.encodel}

fun ancestry {thy} =
  case Theory.LoadableThyData.segment_data{thy=thy, thydataty=tag} of
      NONE => []
    | SOME t => case read t of
                    NONE => raise ERR "ancestry" "Badly encoded data"
                  | SOME sl => sl

fun set_ancestry sl =
  Theory.LoadableThyData.set_theory_data{thydataty = tag, data = write sl}


end
