(* holdoc_init.ml -- initial settings of various category lists *)
(* Keith Wansbrough 2001,2002 *)

(* these are now always initialised from a file; there are no defaults *)

(* modal settings first (these depend on the current mode) *)

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

(* current modal settings *)
let curmodals = ref {
  tYPE_LIST = ref [];
  cON_LIST = ref [];
  fIELD_LIST = ref [];
  lIB_LIST = ref [];
  aUX_LIST = ref [];
  aUX_INFIX_LIST = ref [];
  vAR_PREFIX_LIST = ref [];
  vAR_PREFIX_ALIST = ref [];
  hOL_OP_LIST = ref [];
  hOL_SYM_ALIST = ref [];
  hOL_ID_ALIST = ref [];
  hOL_CURRIED_ALIST = ref [];
  sMART_PREFIX = ref true;
  iNDENT = ref true;
  rULES = ref false;
  cOMMENTS = ref true;
}

(* list of all modes and corresponding settings *)
let modes = ref [("0",!curmodals)]

exception BadDirective

(* new mode is based on current mode, allowing tree-structured creation of modes *)
let new_mode name = (if List.mem_assoc name !modes then
                       (prerr_endline ("Attempt to recreate existing mode "^name);
                        raise BadDirective)
                     else
                       (curmodals := {
                                       tYPE_LIST = ref !(!curmodals.tYPE_LIST);
                                       cON_LIST = ref !(!curmodals.cON_LIST);
                                       fIELD_LIST = ref !(!curmodals.fIELD_LIST);
                                       lIB_LIST = ref !(!curmodals.lIB_LIST);
                                       aUX_LIST = ref !(!curmodals.aUX_LIST);
                                       aUX_INFIX_LIST = ref !(!curmodals.aUX_INFIX_LIST);
                                       vAR_PREFIX_LIST = ref !(!curmodals.vAR_PREFIX_LIST);
                                       vAR_PREFIX_ALIST = ref !(!curmodals.vAR_PREFIX_ALIST);
                                       hOL_OP_LIST = ref !(!curmodals.hOL_OP_LIST);
                                       hOL_SYM_ALIST = ref !(!curmodals.hOL_SYM_ALIST);
                                       hOL_ID_ALIST = ref !(!curmodals.hOL_ID_ALIST);
                                       hOL_CURRIED_ALIST = ref !(!curmodals.hOL_CURRIED_ALIST);
                                       sMART_PREFIX = ref !(!curmodals.sMART_PREFIX);
                                       iNDENT = ref !(!curmodals.iNDENT);
                                       rULES = ref !(!curmodals.rULES);
                                       cOMMENTS = ref !(!curmodals.cOMMENTS);
                                     };
                       modes := (name,!curmodals)::!modes)
                    )

(* changing a mode just means picking out the right modalsettings *)
let change_mode name = (curmodals := List.assoc name !modes)

(* other settings *)
let eCHO = ref true
let rCSID = ref None
let hOLDELIMOPEN  = ref "$" (* [[ *)
let hOLDELIMCLOSE = ref "$" (* ]] *)

