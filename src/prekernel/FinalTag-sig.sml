signature FinalTag =
sig
     type tag

     val axioms_of  : tag -> string Nonce.t list
     val dep_of     : tag -> Dep.dep
     val dest_tag   : tag -> string list * string list
     val isEmpty    : tag -> bool
     val isDisk     : tag -> bool
     val ax_tag     : string Nonce.t -> tag
     val set_dep    : Dep.dep -> tag -> tag
     val read       : string -> tag
     val merge      : tag -> tag -> tag
     val pp_tag     : Portable.ppstream -> tag -> unit
     val pp_to_disk : Portable.ppstream -> tag -> unit

end
