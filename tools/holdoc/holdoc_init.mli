(* holdoc_init.mli -- initial settings of various category lists *)
(* Keith Wansbrough 2001 *)

type modalsettings = {
  tYPE_LIST : string list ref;
  cON_LIST : string list ref;
  fIELD_LIST : string list ref;
  lIB_LIST : string list ref;
  aUX_LIST : string list ref;
  aUX_INFIX_LIST : string list ref;
  vAR_PREFIX_LIST : string list ref;
  vAR_PREFIX_ALIST : (string * string) list ref;
  hOL_OP_LIST : string list ref;
  hOL_SYM_ALIST : (string * string) list ref;
  hOL_ID_ALIST : (string * string) list ref;
  hOL_CURRIED_ALIST : (string * (string * int * bool * bool)) list ref;
  sMART_PREFIX : bool ref;
  iNDENT : bool ref;
  rULES : bool ref;
  cOMMENTS : bool ref;
}

val curmodals : modalsettings ref

val modes : (string * modalsettings) list ref

exception BadDirective

val new_mode : string -> unit

val change_mode : string -> unit

val eCHO : bool ref
val rCSID : string option ref
val hOLDELIMOPEN : string ref
val hOLDELIMCLOSE : string ref

val dir_proc : string -> Hollex.token list -> unit

