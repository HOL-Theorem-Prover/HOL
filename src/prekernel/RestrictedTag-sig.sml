signature RestrictedTag =
sig
     type tag

     val read    : string -> tag
     val isEmpty : tag -> bool
     val isDisk  : tag -> bool
     val merge   : tag -> tag -> tag
     val pp_tag  : Portable.ppstream -> tag -> unit

end
