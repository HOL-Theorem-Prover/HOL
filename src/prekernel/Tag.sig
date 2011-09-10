signature Tag =
sig
     type tag

     val read    : string -> tag
     val read_disk_tag : string list -> tag
     val axioms_of : tag -> string Nonce.t list
     val dest_tag : tag -> string list * string list
     val empty_tag : tag
     val isEmpty   : tag -> bool
     val isDisk    : tag -> bool
     val merge     : tag -> tag -> tag
     val ax_tag    : string Nonce.t -> tag
     val pp_tag    : Portable.ppstream -> tag -> unit
     val pp_to_disk : Portable.ppstream -> tag -> unit

end
