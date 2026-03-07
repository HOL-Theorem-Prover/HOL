signature ProofTraceConverter = sig

val convert: ProofTraceParser.root ProofTraceParser.ptr * ProofTraceParser.heap -> string -> unit

end
