(* holdoc_init.mli -- initial settings of various category lists *)
(* Keith Wansbrough 2001 *)

val tYPE_LIST : string list ref
val cON_LIST : string list ref
val fIELD_LIST : string list ref
val lIB_LIST : string list ref
val aUX_LIST : string list ref
val aUX_INFIX_LIST : string list ref
val vAR_PREFIX_LIST : string list ref
val hOL_OP_LIST : string list ref
val hOL_SYM_ALIST : (string * string) list ref
val hOL_ID_ALIST : (string * string) list ref
val hOL_CURRIED_ALIST : (string * (string * int)) list ref

val eCHO : bool ref

exception BadDirective

val dir_proc : string -> Hollex.token list -> unit

