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
  hOL_OP_LIST : string list ref;
  hOL_SYM_ALIST : (string * string) list ref;
  hOL_ID_ALIST : (string * string) list ref;
  hOL_CURRIED_ALIST : (string * (string * int * bool * bool)) list ref;
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
  hOL_OP_LIST = ref [];
  hOL_SYM_ALIST = ref [];
  hOL_ID_ALIST = ref [];
  hOL_CURRIED_ALIST = ref [];
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
                                       hOL_OP_LIST = ref !(!curmodals.hOL_OP_LIST);
                                       hOL_SYM_ALIST = ref !(!curmodals.hOL_SYM_ALIST);
                                       hOL_ID_ALIST = ref !(!curmodals.hOL_ID_ALIST);
                                       hOL_CURRIED_ALIST = ref !(!curmodals.hOL_CURRIED_ALIST);
                                     };
                       modes := (name,!curmodals)::!modes)
                    )

(* changing a mode just means picking out the right modalsettings *)
let change_mode name = (curmodals := List.assoc name !modes)

(* other settings *)
let eCHO = ref true
let rCSID = ref None
let iNDENT = ref true
let hOLDELIMOPEN  = ref "$" (* [[ *)
let hOLDELIMCLOSE = ref "$" (* ]] *)

open Hollex

let dir_proc n ts =
  let rec go ts =
    match ts with
      (White(_)::ts)   -> go ts
    | (Indent(_)::ts)  -> go ts
    | (Comment(_)::ts) -> go ts
    | (Ident(s,_)::ts) -> s :: go ts
    | (t::ts)          -> prerr_endline ("Unexpected token in list: "^render_token t);
                          raise BadDirective
    | []               -> []
  in
  let rec go2 ts =
    match ts with
      (White(_)::ts)   -> go2 ts
    | (Indent(_)::ts)  -> go2 ts
    | (Comment(_)::ts) -> go2 ts
    | (Ident(s1,_)::White(_)::Str(s2)::ts) -> (s1,s2) :: go2 ts
    | (t::ts)          -> prerr_endline ("Unexpected token in alist: "^render_token t);
                          raise BadDirective
    | []               -> []
  in
  let rec go2nb ts =
    match ts with
      (White(_)::ts)   -> go2nb ts
    | (Indent(_)::ts)  -> go2nb ts
    | (Comment(_)::ts) -> go2nb ts
    | (Ident(s1,_)::White(_)::Str(s2)::White(_)::Ident(s3,true)::White(_)::Ident(s4,true)::White(_)::Ident(s5,true)::ts)
                       -> (s1,(s2,int_of_string s3,bool_of_string s4,bool_of_string s5)) :: go2nb ts
    | (Ident(s1,_)::White(_)::Str(s2)::White(_)::Ident(s3,true)::White(_)::Ident(s4,true)::ts)
                       -> (s1,(s2,int_of_string s3,bool_of_string s4,false)) :: go2nb ts
                          (* default final parameter is =false *)
    | (t::ts)          -> prerr_endline ("Unexpected token in alist(c): "^render_token t);
                          raise BadDirective
    | []               -> []
  in
  let rec goId ts =
    match ts with
      (White(_)::ts)   -> goId ts
    | (Indent(_)::ts)  -> goId ts
    | (Comment(_)::ts) -> goId ts
    | (Str(s)::ts)     -> s
    | (t::ts)          -> prerr_endline ("Unexpected token in alist(c): "^render_token t);
                          raise BadDirective
    | []               -> prerr_endline ("Missing string in RCSID directive");
                          raise BadDirective
  in
  let rec gostr ts =
    match ts with
      (White(_)::ts)   -> gostr ts
    | (Indent(_)::ts)  -> gostr ts
    | (Comment(_)::ts) -> gostr ts
    | (Str(s)::ts)     -> (s,ts)
    | (t::ts)          -> prerr_endline ("Unexpected token in string sequence: "^render_token t);
                          raise BadDirective
    | []               -> prerr_endline ("Missing string in string sequence");
                          raise BadDirective
  in
  let rec goident ts =
    match ts with
      (White(_)::ts)   -> goId ts
    | (Indent(_)::ts)  -> goId ts
    | (Comment(_)::ts) -> goId ts
    | (Ident(s,_)::ts) -> s
    | (t::ts)          -> prerr_endline ("Unexpected token, wanted identifier: "^render_token t);
                          raise BadDirective
    | []               -> prerr_endline ("Missing identifier");
                          raise BadDirective
  in
  match n with
  (* category lists *)
    "TYPE_LIST"       -> !curmodals.tYPE_LIST       := (go ts)  @ !(!curmodals.tYPE_LIST)
  | "CON_LIST"        -> !curmodals.cON_LIST        := (go ts)  @ !(!curmodals.cON_LIST)
  | "FIELD_LIST"      -> !curmodals.fIELD_LIST      := (go ts)  @ !(!curmodals.fIELD_LIST)
  | "LIB_LIST"        -> !curmodals.lIB_LIST        := (go ts)  @ !(!curmodals.lIB_LIST)
  | "AUX_LIST"        -> !curmodals.aUX_LIST        := (go ts)  @ !(!curmodals.aUX_LIST)
  | "AUX_INFIX_LIST"  -> !curmodals.aUX_INFIX_LIST  := (go ts)  @ !(!curmodals.aUX_INFIX_LIST)
  | "VAR_PREFIX_LIST" -> !curmodals.vAR_PREFIX_LIST := (go ts)  @ !(!curmodals.vAR_PREFIX_LIST)
  | "HOL_OP_LIST"     -> !curmodals.hOL_OP_LIST     := (go ts)  @ !(!curmodals.hOL_OP_LIST)
  | "HOL_SYM_ALIST"   -> !curmodals.hOL_SYM_ALIST   := (go2 ts) @ !(!curmodals.hOL_SYM_ALIST)
  | "HOL_ID_ALIST"    -> !curmodals.hOL_ID_ALIST    := (go2 ts) @ !(!curmodals.hOL_ID_ALIST)
  | "HOL_CURRIED_ALIST" -> !curmodals.hOL_CURRIED_ALIST := (go2nb ts) @ !(!curmodals.hOL_CURRIED_ALIST)
  (* other *)
  | "ECHO"            -> eCHO := true
  | "NOECHO"          -> eCHO := false
  | "RCSID"           -> rCSID           := Some(goId ts)
  | "INDENT"          -> iNDENT := true
  | "NOINDENT"        -> iNDENT := false
  | "HOLDELIM"        -> let (s1,ts1) = gostr ts in let (s2,_) = gostr ts1 in
                         hOLDELIMOPEN := s1; hOLDELIMCLOSE := s2
  | "NEWMODE"         -> new_mode (goident ts)
  | "MODE"            -> change_mode (goident ts)
  | _                 -> ()

