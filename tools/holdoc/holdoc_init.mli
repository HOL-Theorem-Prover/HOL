(* holdoc_init.mli -- initial settings of various category lists *)
(* Keith Wansbrough 2001 *)

type curried_info = {
    cy_cmd : string;     (* the TeX command to use *)
    cy_arity : int;      (* the arity ( *before* converting commas) *)
    cy_commas : bool;    (* turn first-level commas into "}{"
                            and remove first-level parens *)
    cy_multiline : bool; (* allow multi-line *)
}

type class_info = {
    cl_cmd : string;           (* the TeX command to use *)
    cl_dosub : bool;           (* do subscripting? *)
    cl_highpri : bool;         (* if class and var, class wins *)
}


(* modal settings first (these depend on the current mode) *)

type modalsettings = {
  cLASSES : (string * class_info) list ref;
  cLASS_IDS_LIST : (string, string) Hashtbl.t;
  vAR_PREFIX_LIST : string list ref;
  vAR_PREFIX_ALIST : (string * string) list ref;
  aUTO_BINDERS : bool ref;
  hOL_SYM_ALIST : (string * string) list ref;
  hOL_SYM_BOL_ALIST : (string * string) list ref;
  hOL_IOPEN_LIST : string list ref;
  hOL_ICLOSE_LIST : string list ref;
  hOL_ID_ALIST : (string * string) list ref;
  hOL_CURRIED_ALIST : (string * curried_info) list ref;
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
val hOLDELIMUNBAL : bool ref

val nonagg_specials : string list ref


val do_directive : Holdocmodel.directive_content0 -> unit
