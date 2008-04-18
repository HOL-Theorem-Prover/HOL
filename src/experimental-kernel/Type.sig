signature Type =
sig

  include FinalType

  val ty_sub        : (hol_type,hol_type) Lib.subst -> hol_type ->
                      hol_type Lib.delta


  (* accessing and manipulating theory information for types *)
  val prim_new_type : {Thy:string, Tyop:string} -> int -> unit
  val prim_delete_type : {Thy:string, Tyop:string} -> unit
  val thy_types : string -> (string * int) list
  val del_segment : string -> unit
  val uptodate_type : hol_type -> bool


end
