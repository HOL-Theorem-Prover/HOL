(* holdoc_init.ml -- initial settings of various category lists *)
(* Keith Wansbrough 2001,2002 *)

(* these are now always initialised from a file; there are no defaults *)
let tYPE_LIST = ref []
let cON_LIST = ref []
let fIELD_LIST = ref []
let lIB_LIST = ref []
let aUX_LIST = ref []
let aUX_INFIX_LIST = ref []
let vAR_PREFIX_LIST = ref []
let hOL_OP_LIST = ref []
let hOL_SYM_ALIST = ref []
let hOL_ID_ALIST = ref []
let hOL_CURRIED_ALIST = ref []

(* other settings *)
let eCHO = ref true
let rCSID = ref None
let iNDENT = ref true

open Hollex
exception BadDirective

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
  match n with
  (* category lists *)
    "TYPE_LIST"       -> tYPE_LIST       := (go ts)  @ !tYPE_LIST
  | "CON_LIST"        -> cON_LIST        := (go ts)  @ !cON_LIST
  | "FIELD_LIST"      -> fIELD_LIST      := (go ts)  @ !fIELD_LIST
  | "LIB_LIST"        -> lIB_LIST        := (go ts)  @ !lIB_LIST
  | "AUX_LIST"        -> aUX_LIST        := (go ts)  @ !aUX_LIST
  | "AUX_INFIX_LIST"  -> aUX_INFIX_LIST  := (go ts)  @ !aUX_INFIX_LIST
  | "VAR_PREFIX_LIST" -> vAR_PREFIX_LIST := (go ts)  @ !vAR_PREFIX_LIST
  | "HOL_OP_LIST"     -> hOL_OP_LIST     := (go ts)  @ !hOL_OP_LIST
  | "HOL_SYM_ALIST"   -> hOL_SYM_ALIST   := (go2 ts) @ !hOL_SYM_ALIST
  | "HOL_ID_ALIST"    -> hOL_ID_ALIST    := (go2 ts) @ !hOL_ID_ALIST
  | "HOL_CURRIED_ALIST" -> hOL_CURRIED_ALIST := (go2nb ts) @ !hOL_CURRIED_ALIST
  (* other *)
  | "ECHO"            -> eCHO := true
  | "NOECHO"          -> eCHO := false
  | "RCSID"           -> rCSID           := Some(goId ts)
  | "INDENT"          -> iNDENT := true
  | "NOINDENT"        -> iNDENT := false
  | _                 -> ()

