signature FinalType =
sig

 eqtype kind
 eqtype hol_type
 type tyvar = string * kind * int (* rank *)

 val mk_vartype    : string -> hol_type
 val mk_vartype_opr : tyvar -> hol_type
 val mk_primed_vartype : string -> hol_type
 val mk_primed_vartype_opr : tyvar -> hol_type
 val gen_tyvar     : unit -> hol_type
 val gen_tyopvar   : kind * int -> hol_type
 val variant_type  : hol_type list -> hol_type -> hol_type
 val variant_tyvar : hol_type list -> tyvar -> tyvar
 val prim_variant_type : hol_type list -> hol_type -> hol_type
 val dest_vartype  : hol_type -> string
 val dest_vartype_opr : hol_type -> tyvar
 val is_vartype    : hol_type -> bool
 val is_gen_tyvar  : hol_type -> bool

 val mk_type       : string * hol_type list -> hol_type
 val dest_type     : hol_type -> string * hol_type list
 val is_type       : hol_type -> bool
 val mk_thy_type   : {Thy:string, Tyop:string, Args:hol_type list} -> hol_type
 val dest_thy_type : hol_type -> {Thy:string, Tyop:string, Args:hol_type list}

 val mk_con_type   : string -> hol_type
 val mk_thy_con_type : {Thy:string, Tyop:string} -> hol_type
 val dest_con_type : hol_type -> string * kind * int
 val dest_thy_con_type : hol_type -> {Thy:string, Tyop:string, Kind:kind,
                                       Rank:int}
 val is_con_type   : hol_type -> bool

 val mk_app_type   : hol_type * hol_type -> hol_type
 val list_mk_app_type : hol_type * hol_type list -> hol_type
 val dest_app_type : hol_type -> hol_type * hol_type
 val strip_app_type: hol_type -> hol_type * hol_type list
 val is_app_type   : hol_type -> bool

 val mk_univ_type  : hol_type * hol_type -> hol_type
 val list_mk_univ_type : hol_type list * hol_type -> hol_type
 val dest_univ_type: hol_type -> hol_type * hol_type
 val strip_univ_type : hol_type -> hol_type list * hol_type
 val is_univ_type  : hol_type -> bool

 val mk_abs_type   : hol_type * hol_type -> hol_type
 val list_mk_abs_type : hol_type list * hol_type -> hol_type
 val dest_abs_type : hol_type -> hol_type * hol_type
 val strip_abs_type : hol_type -> hol_type list * hol_type
 val is_abs_type   : hol_type -> bool

 val kind_of       : hol_type -> kind
 val rank_of       : hol_type -> int
 val aconv_ty      : hol_type -> hol_type -> bool
 val beta_conv_ty  : hol_type -> hol_type
 val deep_beta_conv_ty : hol_type -> hol_type
 val abconv_ty     : hol_type -> hol_type -> bool

 val decls         : string -> {Thy:string, Tyop:string} list
 val op_arity      : {Thy:string, Tyop:string} -> int option
 val op_kind       : {Thy:string, Tyop:string} -> kind option
 val op_rank       : {Thy:string, Tyop:string} -> int option

 val type_vars     : hol_type -> hol_type list
 val type_varsl    : hol_type list -> hol_type list
 val type_vars_lr  : hol_type -> hol_type list
 val type_var_in   : hol_type -> hol_type -> bool
 val exists_tyvar  : (hol_type -> bool) -> hol_type -> bool
 val polymorphic   : hol_type -> bool
 val universal     : hol_type -> bool
 val abstraction   : hol_type -> bool
 val kind_rank_compare : (kind * int) * (kind * int) -> order
 val tyvar_compare : tyvar * tyvar -> order
 val compare       : hol_type * hol_type -> order
 val tyvar_eq      : tyvar -> tyvar -> bool
 val type_eq       : hol_type -> hol_type -> bool
 val empty_tyset   : hol_type  HOLset.set

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
                             -> (hol_type,hol_type) Lib.subst
                             -> (hol_type,hol_type) Lib.subst
 val raw_match_type: hol_type -> hol_type 
                      -> (hol_type,hol_type) Lib.subst * hol_type list
                      -> (hol_type,hol_type) Lib.subst * hol_type list
(*
 val type_pmatch : hol_type HOLset.set -> {redex : hol_type, residue : hol_type} list ->
                   hol_type -> hol_type ->
                   (hol_type,hol_type)Lib.subst *
                   ((hol_type,hol_type)Lib.subst * hol_type * hol_type) list ->
                   (hol_type,hol_type)Lib.subst *
                   ((hol_type,hol_type)Lib.subst * hol_type * hol_type) list
 val separate_insts_ty : (hol_type,hol_type)Lib.subst ->
                         {redex : hol_type, residue : int} list *
                         (hol_type,hol_type)Lib.subst
 val all_abconv : hol_type list -> hol_type list -> bool
 val type_homatch : hol_type HOLset.set ->
                    (hol_type,hol_type)Lib.subst *
                    ((hol_type,hol_type)Lib.subst * hol_type * hol_type) list ->
                    (hol_type,hol_type)Lib.subst
 val ho_match_type1 : hol_type HOLset.set -> hol_type -> hol_type
                      -> (hol_type,hol_type)Lib.subst *
                         ((hol_type,hol_type)Lib.subst * hol_type * hol_type) list
                      -> (hol_type,int)Lib.subst * (hol_type,hol_type)Lib.subst
 val ho_match_type0 : hol_type HOLset.set -> hol_type -> hol_type
                      -> (hol_type,int)Lib.subst * (hol_type,hol_type)Lib.subst
 val ho_match_type  : hol_type HOLset.set -> hol_type -> hol_type
                      -> (hol_type,hol_type)Lib.subst
*)

 val pp_raw_type    : ppstream -> hol_type -> unit
 val type_to_string : hol_type -> string
end
