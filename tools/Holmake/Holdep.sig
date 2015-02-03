signature Holdep =
sig


val main : { assumes : string list,
             includes : string list,
             debug : bool,
             fname : string } ->
           string list

val encode_for_HOLMKfile : {tgt : string, deps : string list} -> string


end
