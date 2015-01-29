signature Holdep =
sig


val main : { assumes : string list,
             includes : string list,
             debug : bool,
             fname : string } -> string


end
