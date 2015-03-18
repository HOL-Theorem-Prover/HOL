signature Tag =
sig
     type tag

     val axioms_of : tag -> string Nonce.t list
     val dep_of : tag -> Dep.dep 
     val dest_tag  : tag -> string list * string list 
     val empty_tag : tag
     val isEmpty   : tag -> bool
     val isDisk    : tag -> bool
     val ax_tag     : string Nonce.t -> tag
     val set_dep    : Dep.dep -> tag -> tag
     val read       : string -> tag 

     (* Track the extra information passed through the inference rules *)
     val collapse       : tag -> tag
     val merge          : tag -> tag -> tag
     val trackconj      : tag -> tag -> tag
     val trackconjunct1 : tag -> tag
     val trackconjunct2 : tag -> tag

     (* Reading and printing *)
     val read_disk_tag : Dep.depdisk * string list -> tag
     val pp_tag     : Portable.ppstream -> tag -> unit
     val pp_to_disk : Portable.ppstream -> tag -> unit

end
