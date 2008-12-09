val sigsToHtml    : string -> string -> string list -> string -> string 
                    -> (string * string) list -> string * string -> unit
val printHTMLBase : string -> string -> string -> 
                    (Database.entry -> bool) -> string ->
                    string * string -> unit
