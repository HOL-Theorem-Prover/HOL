(* ===================================================================== *)
(* FILE          : Type.sig                                              *)
(* DESCRIPTION   : HOL types.                                            *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* UPDATE        : October 94. Type signature implementation moved from  *)
(*                 symtab.sml, which is now gone.                        *)
(* Modified      : September 22, 1997, Ken Larsen                        *)
(*                 April 12, 1998, Konrad Slind                          *)
(*                 July, 2000, Konrad Slind                              *)
(* ===================================================================== *)

signature Type =
sig

 eqtype hol_type

 val mk_vartype    : string -> hol_type
 val dest_vartype  : hol_type -> string
 val is_vartype    : hol_type -> bool

 val mk_type       : {Tyop: string, Args:hol_type list} -> hol_type
 val dest_type     : hol_type -> {Tyop:string, Args:hol_type list}
 val is_type       : hol_type -> bool
 val mk_thy_type   : {Thy:string, Tyop:string, Args:hol_type list} -> hol_type
 val dest_thy_type : hol_type -> {Thy:string, Tyop:string, Args:hol_type list}

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

 val type_subst    : (hol_type,hol_type) Lib.subst -> hol_type -> hol_type
 val match_type    : hol_type -> hol_type -> (hol_type,hol_type) Lib.subst
end;
