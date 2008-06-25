(* holdoc_init.ml -- initial settings of various category lists *)
(* Keith Wansbrough 2001,2002 *)

open Holdocmodel

(* these are now always initialised from a file; there are no defaults *)

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

(* current modal settings *)
let curmodals = ref {
  cLASSES = ref [
    ("TYPE"     , { cl_cmd = "\\tstype"    ; cl_dosub = false; cl_highpri = false });
    ("CON"      , { cl_cmd = "\\tscon"     ; cl_dosub = false; cl_highpri = true  });
    ("FIELD"    , { cl_cmd = "\\tsfield"   ; cl_dosub = false; cl_highpri = false });
    ("LIB"      , { cl_cmd = "\\tslib"     ; cl_dosub = true ; cl_highpri = true  });
    ("AUX"      , { cl_cmd = "\\tsaux"     ; cl_dosub = false; cl_highpri = true  });
    ("AUX_INFIX", { cl_cmd = "\\tsauxinfix"; cl_dosub = false; cl_highpri = true  });
    ("HOL_OP"   , { cl_cmd = "\\tsholop"   ; cl_dosub = false; cl_highpri = false });
  ];
  cLASS_IDS_LIST = Hashtbl.create 100;
  vAR_PREFIX_LIST = ref [];
  vAR_PREFIX_ALIST = ref [];
  aUTO_BINDERS = ref true;
  hOL_SYM_ALIST = ref [];
  hOL_SYM_BOL_ALIST = ref [];
  hOL_IOPEN_LIST = ref [];
  hOL_ICLOSE_LIST = ref [];
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

let copy_table t0 =
  let t = Hashtbl.create 100 in
  Hashtbl.iter (fun k v -> Hashtbl.add t k v) t0;
  t

(* new mode is based on current mode, allowing tree-structured creation of modes *)
let new_mode name = (if List.mem_assoc name !modes then
                       (prerr_endline ("Attempt to recreate existing mode "^name);
                        raise BadDirective)
                     else
                       (curmodals := {
                                       cLASSES = ref !(!curmodals.cLASSES);
                                       cLASS_IDS_LIST = copy_table !curmodals.cLASS_IDS_LIST;
                                       vAR_PREFIX_LIST = ref !(!curmodals.vAR_PREFIX_LIST);
                                       vAR_PREFIX_ALIST = ref !(!curmodals.vAR_PREFIX_ALIST);
                                       aUTO_BINDERS = ref !(!curmodals.aUTO_BINDERS);
                                       hOL_SYM_ALIST = ref !(!curmodals.hOL_SYM_ALIST);
                                       hOL_SYM_BOL_ALIST = ref !(!curmodals.hOL_SYM_BOL_ALIST);
                                       hOL_IOPEN_LIST = ref !(!curmodals.hOL_IOPEN_LIST);
                                       hOL_ICLOSE_LIST = ref !(!curmodals.hOL_ICLOSE_LIST);
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
let hOLDELIMUNBAL = ref false


(* this is a lexer parameter, and is a bit special:
   symbolic identifiers that contain nonaggregating characters; user-extensible *)
let nonagg_specials = ref ["()"; "[]"; ".."; "..."]


let do_directive : directive_content0 -> unit
    = function
      | DirThunk f -> f ()
      | DirVARS is -> ()  (* ignore *)
      | DirRCSID s -> rCSID := Some s
