signature Tag =
sig
     type tag

     val read    : string -> tag
     val read_disk_tag : Dep.depdisk * string list -> tag
     val axioms_of : tag -> string Nonce.t list
     val dest_tag  : tag -> string list * string list
     val empty_tag : tag
     val isEmpty   : tag -> bool
     val isDisk    : tag -> bool
     val merge     : tag -> tag -> tag
     val ax_tag    : string Nonce.t -> tag
     val pp_tag    : Portable.ppstream -> tag -> unit
     val pp_to_disk : Portable.ppstream -> tag -> unit

     (* Tracking dependencies *)
     val dep_of : tag -> Dep.dep 
     val give_depid_tag : Dep.depid -> tag -> tag (* on Theory.save_thm *)
     val merge_dep : tag -> tag
     val merge_conj : tag -> tag -> tag
     val merge_conjunct1: tag -> tag
     val merge_conjunct2: tag -> tag

end
