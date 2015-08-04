signature Holdep =
sig

exception Holdep_Error of string
val main : { assumes : string list,
             includes : string list,
             diag : string -> unit,
             fname : string } ->
           {tgt : string, deps : string list}

val encode_for_HOLMKfile : {tgt : string, deps : string list} -> string


end
