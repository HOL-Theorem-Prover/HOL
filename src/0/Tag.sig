signature Tag =
sig
     type tag

     val merge     : tag -> tag -> tag
     val read      : string -> tag
     val axioms_of : tag -> string ref list

     val pp        : Portable.ppstream -> tag -> unit
     val pp_to_disk: Portable.ppstream -> tag -> unit

     val is_std    : tag -> bool
     val init : tag ref -> tag ref -> tag ref 
                 -> (string -> tag) ref -> (string ref -> tag) ref -> unit

end 
