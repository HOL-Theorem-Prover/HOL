signature Type =
sig

 eqtype hol_type

  val mk_vartype   : string -> hol_type
  val dest_vartype : hol_type -> string
  val is_vartype   : hol_type -> bool
  val mk_type      : {Tyop: string, Args:hol_type list} -> hol_type
  val dest_type    : hol_type -> {Tyop:string, Args:hol_type list}
  val polymorphic  : hol_type -> bool
  val type_lt      : hol_type -> hol_type -> bool
  val type_compare : hol_type -> hol_type -> order

  datatype 'a delta = SAME | DIFF of 'a
  val ty_sub     : (hol_type,hol_type) Lib.subst -> hol_type -> hol_type delta
  val type_subst : (hol_type,hol_type) Lib.subst -> hol_type -> hol_type
  val type_vars  : hol_type -> hol_type list
  val type_varsl : hol_type list -> hol_type list

  val dummy : hol_type

  (* function types and booleans *)
  val -->     : hol_type * hol_type -> hol_type  (* infixr 3 --> *)
  val dom_rng : hol_type -> hol_type * hol_type  (* inverts -->  *)
  val bool    : hol_type
  val alpha   : hol_type  (* Type variables *)
  val beta    : hol_type

  (* matching *)
  val type_reduce : hol_type -> hol_type
       -> (hol_type,hol_type) Lib.subst -> (hol_type,hol_type) Lib.subst
  val match_type :  hol_type -> hol_type -> (hol_type,hol_type) Lib.subst

  (* Forward reference *)
  val init : ({Tyop: string, Args:hol_type list} -> hol_type)
             -> (string -> int)
               -> unit

  (* Information hiding *)
  val Theory_init :({name:string,revision:int} * hol_type list -> hol_type)ref
                -> (hol_type -> {name:string,revision:int} * hol_type list)ref
              -> unit

end;
