signature ProofTraceConverter = sig

include ProofTraceParser
val convert: root ptr * heap -> string -> unit

end
