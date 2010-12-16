signature FinalType =
sig

 eqtype hol_type

 val mk_vartype    : string -> hol_type
 val gen_tyvar     : unit -> hol_type
 val dest_vartype  : hol_type -> string
 val is_vartype    : hol_type -> bool
 val is_gen_tyvar  : hol_type -> bool

 val mk_type       : string * hol_type list -> hol_type
 val dest_type     : hol_type -> string * hol_type list
 val is_type       : hol_type -> bool
 val mk_thy_type   : {Thy:string, Tyop:string, Args:hol_type list} -> hol_type
 val dest_thy_type : hol_type -> {Thy:string, Tyop:string, Args:hol_type list}

 val decls         : string -> {Thy:string, Tyop:string} list
 val op_arity      : {Thy:string, Tyop:string} -> int option

 val type_vars     : hol_type -> hol_type list
 val type_varsl    : hol_type list -> hol_type list
 val type_var_in   : hol_type -> hol_type -> bool
 val exists_tyvar  : (hol_type -> bool) -> hol_type -> bool
 val polymorphic   : hol_type -> bool
 val compare       : hol_type * hol_type -> order

 val -->           : hol_type * hol_type -> hol_type  (* infixr 3 --> *)
 val dom_rng       : hol_type -> hol_type * hol_type  (* inverts -->  *)
 val bool          : hol_type
 val ind           : hol_type
 val alpha         : hol_type
 val beta          : hol_type
 val gamma         : hol_type
 val delta         : hol_type
 val etyvar        : hol_type
 val ftyvar        : hol_type

 val type_subst    : (hol_type,hol_type) Lib.subst -> hol_type -> hol_type

 val match_type    : hol_type -> hol_type -> (hol_type,hol_type) Lib.subst

 val match_type_restr : hol_type list -> hol_type -> hol_type
                        -> (hol_type,hol_type) Lib.subst

 val match_type_in_context : hol_type -> hol_type
                             -> (hol_type,hol_type)Lib.subst
                             -> (hol_type,hol_type)Lib.subst
 val raw_match_type: hol_type -> hol_type
                      -> (hol_type,hol_type) Lib.subst * hol_type list
                      -> (hol_type,hol_type) Lib.subst * hol_type list

 val type_size : hol_type -> int

 val ty_sub        : (hol_type,hol_type) Lib.subst -> hol_type ->
                      hol_type Lib.delta


 (* accessing and manipulating theory information for types *)
 val prim_new_type : {Thy:string, Tyop:string} -> int -> unit
 val prim_delete_type : {Thy:string, Tyop:string} -> unit
 val thy_types : string -> (string * int) list
 val del_segment : string -> unit
 val uptodate_type : hol_type -> bool



end
