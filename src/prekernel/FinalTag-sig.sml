signature FinalTag =
sig
     type tag

     val read    : string -> tag
     val dest_tag : tag -> string list * string list
     val merge   : tag -> tag -> tag
     val isEmpty : tag -> bool
     val isDisk  : tag -> bool
     val pp_tag  : Portable.ppstream -> tag -> unit

end
