(* lts_to_latex.ml -- turn LTS (in HOL) into LaTeX code *)
(* Keith Wansbrough 2001 *)

open Hollex

exception Trailing (* there is trailing info in the file *)
exception BadLabel

(* build a fast stream of tokens from lexed stdin *)
let tokstream =
  let lexbuf = Lexing.from_channel stdin in
  relheader lexbuf ;
  let f _ = (* I hope it is valid to assume that *all*
               tokens are requested, in ascending order! *)
    try
      Some (reltoken lexbuf)
    with
      Finished -> None
  in
  Stream.from f


(* a useful helper *)
let isIndent t =
  match t with
    Indent(n) -> true
  | _         -> false

let render_token t =
  match t with
    Ident(s,_) -> "I:"^s
  | Indent(n)  -> "\nN:"^(String.make n '>')
  | White(s)   -> "W:"^s
  | Comment(s) -> "C:(*"^s^"*)-C"
  | Sep(s)     -> "S:"^s

let print_tokenline toks =
    let f t = print_string ((render_token t)^" ")
    in
    ignore (List.map f toks);
    print_newline()



(*
The standard format for a rule is:

  (! universally-quantified variables.

  rule_name /* rule_category (* optional rule description *) */
    rule_lhs
  -- rule_label -->
    rule_rhs

  <==

    rule_side_condition

  (*
  optional rule commentary
  *)
  )

Note that blank lines are to be respected, and preferably indents also.

LaTeX is permitted in comments, and Hol source can be enclosed in
double square brackets like this: [[Flags(T,F)]].

*)

(* now for the parsers *)


type rule =
    Rule of string list * string * string * string option (* v, n, cat, desc, *)
        * token list list * token list * token list list (* lhs, lab, rhs, *)
        * token list list * string option (* side, comm *)


let rec parse_line = parser
    [< 'Indent(n); e = parse_line1 >] -> Indent(n) :: e

and parse_line1 = parser
    [< 't when not (isIndent t) ; e = parse_line1 >] -> t :: e
  | [<>]                                             -> []

and parse_chunk = parser
    [< 'Indent(n); c = parse_chunk1 n >] -> c

and parse_chunk1 n = parser
    [< 't when not (isIndent t) ; e = parse_line1 ;
       c = parse_chunk >] -> (Indent(n) :: t :: e) :: c
  | [<>]                  -> []

and optcomm = parser
    [< 'Comment(c) >] -> Some c
  | [<>]              -> None

and sp1 = parser
    [< 'White(s)  ; s1 = sp >] -> White(s)   :: s1
  | [< 'Comment(c); s1 = sp >] -> Comment(c) :: s1
                                                 
and sp = parser
    [< 'White(s)  ; s1 = sp >] -> White(s)   :: s1
  | [< 'Comment(c); s1 = sp >] -> Comment(c) :: s1
  | [<>]                       -> []

and wopt = parser
    [< 'White(s)  ; s1 = wopt >] -> White(s)   :: s1
  | [<>]                         -> []

and sp' = parser
    [< 'White(s)  ; s1 = sp' >] -> White(s)   :: s1
  | [< 'Indent(n) ; s1 = sp' >] -> Indent(n)  :: s1
  | [< 'Comment(c); s1 = sp' >] -> Comment(c) :: s1
  | [<>]                        -> []

and optind = parser
    [< 'Indent(n) ; is = optind >] -> Indent(n) :: is
  | [<>]                           -> []

(* and parse_rule = parser [<>] -> Rule([],"","",None,[],[],[],[],None) *)

and parse_rule = parser
    [< 'Sep("("); _ = sp; r1 = parse_rule1 >] -> r1
  | [<>] -> raise (Stream.Error("rule begin: `('"));
and parse_rule1 = parser
    [< 'Ident("!",_); v = rule_vars; _ = sp; 'Sep(".") ?? "."; _ = sp; 
       'Indent(_);
       (n,cat,desc) = rule_name;
       l_lab_r = parse_chunk;
       'Indent(_);
       _ = sp'; 'Ident("<==",_) ?? n^": <=="; _ = sp;
       'Indent(_);
       side = parse_chunk;
       'Indent(_); _ = optind;
       comm = optcomm;
       _ = optind;
       _ = sp; 'Sep(")") ?? n^": rule end: `)'"; _ = sp >]
      -> let rec isLab ts =
            match ts with
              (Indent(_)     :: ts) -> isLab ts
            | (White(_)      :: ts) -> isLab ts
            | (Ident("--",_) :: _ ) -> true
            | _                   -> false
         in
         let rec go c lhs =
            match c with
              (x::xs) when isLab x -> (List.rev lhs,x,xs)
            | (x::xs)              -> go xs (x::lhs)
            | _                    -> ([],[],[])
         in
         let (lhs,lab,rhs) = go l_lab_r []
         in
         Rule(v,n,cat,desc,lhs,lab,rhs,side,comm)
  | [<>] -> raise (Stream.Error("!"));

and rule_vars = parser
    [< 'White(_)  ; r = rule_vars >] -> r
  | [< 'Comment(_); r = rule_vars >] -> r
  | [< 'Ident(s,_); r = rule_vars >] -> s :: r
  | [<>]                             -> []

and rule_name = parser
    [< 'Indent(_); 'Ident(n,_) ?? "rule name"; _ = sp; 'Ident("/*",_) ?? "/*"; _ = sp; 'Ident(cat,_) ?? "category"; _ = wopt;
       desc = optcomm; _ = sp; 'Ident("*/",_) ?? "*/"; _ = sp >]
      -> (n,cat,desc)
  | [<>] -> raise (Stream.Error("rule name on new line"));


and parse_rules_and_process p = parser
    [< _ = sp'; rs = parse_rules_ap1 p >] -> rs
and parse_rules_ap1 p = parser
    [< 'Sep("("); _ = sp; r = (function ts -> p (parse_rule1 ts)); _ = sp';
       rs = parse_rules_ap2 p >] -> r :: rs
  | [<>]                         -> []
and parse_rules_ap2 p = parser
    [< 'Ident("/\\",_); _ = sp';
       rs = parse_rules_ap1 p >] -> rs
  | [<>]                         -> []

(* let's do this thing *)

let grab_rules () =
  let rules = parse_rules_ap1 (function x -> x) tokstream
  in
  if Stream.peek tokstream != None then
    raise Trailing
  else
    rules


(* type rule =
    Rule of string list * string * string * string opt (* v, n, cat, desc, *)
        * token list list * token list * token list list (* lhs, lab, rhs, *)
        * token list list * string opt (* side, comm *)
 *)

let print_rule (Rule(v,n,cat,desc,lhs,lab,rhs,side,comm)) =
  print_string ("Rule "^n^" ("^cat^(match desc with Some d -> " "^d | None -> "")^")\n");
  print_string "Vars:\n";
  ignore (List.map (function s -> print_string (s^" ")) v);
  print_newline() ;
  print_string "LHS:\n";
  ignore (List.map print_tokenline lhs);
  print_string "Label:\n";
  print_tokenline lab;
  print_string "RHS:\n";
  ignore (List.map print_tokenline rhs);
  print_string "Side:\n";
  ignore (List.map print_tokenline side);
  print_string (match comm with
                  Some c -> "Comments:\n"^c^"\n"
               |  None   -> "");
  print_newline()


let texify_list =
  [('_', "\\_")
  ;('~', "\\neg ")
  ;('$', "\\$")
  ;('%', "\\%")
  ;('&', "\\&")
  ;('\\', "\\backslash ")
  ;('^', "\\hat{\\phantom{x}}")
  ;('{', "\\{")
  ;('}', "\\}")
  ]

let texify s =
  let go c =
    try List.assoc c texify_list
    with Not_found -> String.make 1 c
  in
  let mapString f s =
    let rec mapS f i n s =
      if i>=n then [] else f (String.get s i) :: mapS f (i+1) n s
    in
    mapS f 0 (String.length s) s
  in
  String.concat "" (mapString go s)



(* the patterns and lists below are all due to munge_lexer.mll and
   need updating *)

let is_rule s = try 
                  (String.index s '.' ) <> (String.length s) -1
                with
                  Not_found -> false

let is_type s = List.mem s 
[ "fd"            ;         
  "ip"            ;   
  "port"          ;   
  "error"         ;   
  "netmask"       ;   
  "ifid"          ;   
  "sockopt"       ;   
  "int"           ;   
  "bool"          ;   
  "string"        ;   
  "list"          ;   
  "err"           ;   
  "void"          ;   
  "set"           ;   
  "ipBody"        ;   
  "msg"           ;   
  "ifd"           ;   
  "flags"         ;   
  "socket"        ;   
  "boxid"         ;   "hostid" ;
  "boxThreadState";   "hostThreadState" ;
  "box"           ;   "host" ;
  "network" ;
  "exn"  ; 
  "lift"  ; 
  "ref"  ;
  "msg-ok" ;
  "ifd-set-ok";
  "socket-ok";
  "msg-oq-ok";
  "box-ok" ; "host-ok" ;
] 


let is_con s = List.mem s 
[ "EACCES"             ;
  "EADDRINUSE"         ;
  "EADDRNOTAVAIL"      ;
  "EAGAIN"             ;
  "EBADF"              ;
  "ECONNREFUSED"       ;
  "EHOSTUNREACH"       ;
  "EINTR"              ;
  "EINVAL"             ;
  "EMFILE"             ;
  "EMSGSIZE"           ;
  "ENFILE"             ;
  "ENOBUFS"            ;
  "ENOMEM"             ;
  "ENOTCONN"           ;
  "ENOTSOCK"           ;
  "EPERM"              ;
  "EDESTADDRREQ"  ; 
  "EISCONN"  ; 
  "EWOULDBLOCK"  ; 
  "ENETUNREACH"  ; 
  "BadInjection" ;
  "lo"                 ;
  "eth0"               ;
  "eth1"               ;
  "true"         ;
  "false"         ;
  "nil"                ;
  "OK"                 ;  
  "Fail"               ;
  "UDP"                ;
  "IP"                 ;
  "IF"                 ;
  "Flags"              ;
  "Sock"               ;
  "alan"               ;
  "emil"               ;
  "john"               ;
  "kurt"               ;
  "astrocyte"          ;
  "Run"                ;
  "Term"               ;
  "Ret"                ;
  "RET"                ;
  "Sendto2"            ;
  "Recvfrom2"          ;
  "Select2"            ;
  "Print2"             ;
  "Box"                ; "Host" ;
  "Lift"  ;
  "Star"  ;
  "c" ;
  "RetOK";
  "RetFail";
  "Op2" ;
  "SO_BSDCOMPAT"       ;
  "SO_REUSEADDR"       ;
  "ICMP_HOST_UNREACH"  ;
  "ICMP_PORT_UNREACH"  ;
  "ICMP_X_UNREACH"  ;
  "Match_failure"  
]


let is_lib s = List.mem s [
  "socket"      ;
  "bind"        ;
  "connect"     ;
  "disconnect"  ;
  "getsockname" ;
  "getpeername" ;
  "geterr"      ;
  "getsockopt"  ;
  "setsockopt"  ;
  "sendto"      ;
  "recvfrom"    ;
  "close"       ;
  "select"      ;
  "getifaddrs"  ;
  "exit"        ;
  "print_endline_flush" ;
  "port_of_int"      ;
  "int_of_port"      ;
  "ip_of_string"     ;
  "iplift_of_string" ;
  "string_of_iplift" ;
]


let is_aux s = List.mem s 
 [ "autobind" ;
  "lookup"   ;
  "outroute" ;
  "socks"    ;
  "sockfd"  ;
  "sockfds"  ;
  "unused"   ;
  "ephemeral";
  "privileged";
  "ephemeralErrors" ;
  "reuseaddr";
  "bsdcompat";
  "setbsdcompat" ;
  "setreuseaddr" ;
  "UDPpayloadMax" ;
  "orderings" ;
  "size"  ;
  "Con" ;
  "arity" ;
  "store"  ; 
  "closed";
  "localhost";
  "Loopback" ;
  "loop" ;
  "LOOPBACK"  ; 
  "MARTIAN"  ; 
  "LOCAL"  ; 
  "MCAST"  ; 
  "MULTICAST"  ; 
  "BADCLASS"  ; 
  "ZERONET"  ; 
  "LIB"  ; 
  "LIBEX"  ; 
  "SocketUDP"  ; 
  "TinyStdio"  ; 
  "enqueue"  ; 
  "dequeue"  ; 
  "dosend"  ; 
  "boxids" ; "hostids" ;
  "threadids"  ;
  "btsType" ; "htsType" ;
  "RET" ;
  "CALL";
  "TAU" ;
  "PROG" ;
  "match" ;
  "score" ;
  "martian"  ; 
  "loopback"  ; 
  "Lbox"  ; "Lhost" ;
  "Lnetwork"  ; 
  "Lthread"  ; 
  "function"  ; 
  "let"  ; 
  "raise"  ; 
  "try"  ; 
  "while"  ; 
  "done";
  "rec" ;
  "if" ;
  "iserr";
  "isterm" ;
  "Alan";
  "Kurt";
  "console" ;
  "succeed" ;
  "enter2" ;
(*  "exit";  clashes with is_lib *)
  "fail";
  "badfail";
  "accept";
  "emit";
  "slowsucceed";
  "slowfail";
  "slowintr";
  "slowbadfail";
  "internaldelivery";
  "disjoint_addr";
  "dom";
  "instep";
  "Crash";
  "crash";
  "map"
 ] 


let is_aux_infix s = List.mem s 
 [ "and";
   "or" ;
   "else" ;
   "then" ;
   "do";
  "in";
   "with";
   "ref"
  ] 

let is_var_prefix s = List.mem s
[ "v" ;
  "f"   ; 
  "ifds" ; 
  "t"   ; 
  "s"   ; 
  "oq"  ; 
  "oqf" ; 
  "fd"  ; 
  "i"   ; 
  "p"   ; 
  "e"   ; 
  "tm"  ; 
  "mq"  ; 
  "is"  ; 
  "ps"  ; 
  "es"  ; 
  "tms" ; 
  "E"   ;
  "F"   ; 
  "H"   ; 
  "Q"   ;
  "OP"  ;
  "ifid";
  "iset";
  "iprimary";
  "netmask";
  "readseq" ;
  "writeseq" ;
  "opt" ;
  "iflist" ;
  "T" ;
  "TL" ;
  "data"  ; 
  "ra"  ; 
  "bc"  ; 
  "body" ;
  "nb"  ; 
  "nm"  ; 
  "mtch";
  "expr";
  "fds"
]


let is_var s = (Str.string_match 
                  (Str.regexp "\([A-Za-z]+\)[0-9]*[']*")
                  s
                  0 ) &&
               (Str.match_end() = String.length s) && 
               (is_var_prefix (Str.matched_group 1 s))

let subscript_var s = 
  let _ = (Str.string_match 
             (Str.regexp "\([A-Za-z]+\)\([0-9]*\)\([']*\)")
             s
             0 ) in 
  if "" <> (Str.matched_group 2 s) then 
    ((Str.matched_group 1 s)^(Str.matched_group 3 s)^"_{"^(Str.matched_group 2 s)^"}")
  else 
    (Str.matched_group 1 s)^(Str.matched_group 3 s)

let extra_left_space s = if List.mem s  [
  "done";
  "list"        ;
  "set"  ;
  "err"  ;
  "store";
  "closed";
  "ref";
  "msg-ok" ;
  "msg-oq-ok" ;
  "ifd-set-ok";
  "socket-ok";
  "box-ok"; "host-ok" ;
  "network" 
] then "\\," else ""


let extra_right_space s = if List.mem s  [
  "Select2";
  "Ret";
  "Sendto2";
  "Recvfrom2";
  "Print2";
  "console";
  "reuseaddr";
  "bsdcompat";
  "setbsdcompat" ;
  "setreuseaddr" ;
  "if";
  "while";
  "function";
  "try";
  "let";
  "rec";
  "raise";
  "Fail"        ;
  "disconnect"  ;
  "getsockname" ;
  "getpeername" ;
  "geterr"      ;
  "close"       ;
  "exit"        ;
  "lookup"      ;
  "print_endline_flush" ;
  "port_of_int" ;
  "ip_of_string" 
] then "\\;" else ""


let space s = 
  (extra_left_space s)^s^(extra_right_space s)

let write_unseen_string s = prerr_endline ("  \"" ^ s ^ "\"  ; ")

let transform s = 
  let s' = texify s and
      lsp = extra_left_space s and
      rsp = extra_right_space s in
  let sps' = lsp ^ s' ^ rsp in
      
  if (is_rule s) then                 "\\tsrule{"^sps'^"}" else 
  if (is_con s) then                  "\\tscon{"^sps'^"}" else 
  if (is_aux s) then                  "\\tsaux{"^sps'^"}" else 
  if (is_aux_infix s) then            "\\tsaux{\\ "^sps'^"\\ }" else 
  if (is_type s) then               "\\tstype{"^sps'^"}" else 
  if (is_lib s) then                "\\tslib{"^sps'^"}" else 
  if (is_var s) then                "\\tsvar{"^sps'^"}" else
  (write_unseen_string s ; (""^s'^""))


let holsyms =
  [ ("/\\","\\Mand ")
  ; ("\\/","\\Mor ")
  ; ("<|","\\langle\\![")
  ; ("|>","]\\!\\rangle ")
  ; ("!","\\forall ")
  ; ("?","\\exists ")
  ; ("?!","\\exists!")
  ; ("==>","\\MArrow{}")
  ; ("<=","\\leq ")
  ; (">=","\\geq ")
  ; ("<>","\\neq ")
(*  ; ("^", "\\Mcaret{}") *)
                             (* Mquotedstring *)
(*  ; ("-->","\\Maarrow{}") *)
  ; ("->","\\Marrow{}")
  ; ("<=>","\\MDArrow{}")
(*   ; (";","\\Msemicolon{}")
  ; (";;","\\Msemisemicolon{}")
  ; ("::=","\\Mcce{}")
  ; (":=","\\Mce{}") *)
  ; ("::","\\Mcoloncolon{}")
  ; (":","\\Mcolon{}")
  ; ("[]","\\Mbrackets{}")
  ]

let holids =
  [ ("SOME","\\Mcaret{}")
  ; ("NONE","*")
  ; ("IN","\\in ")
  ; ("INTER","\\cap ")
  ; ("EMPTY","\\emptyset ")
  ; ("one","()")
  ; ("SUBSET","\\subseteq ")
  ] 

(* we return you to your regular programme *)


let mident s = (* munge alphanumeric identifier *)
(*  "\\tsvar{"^texify s^"}" *)
  try List.assoc s holids
  with Not_found -> transform s

let msym s = (* munge symbolic identifier *)
   try List.assoc s holsyms
   with Not_found -> texify s

let mtok t =
  match t with
    Ident(s,true)  -> mident s
  | Ident(s,false) -> msym s
  | Indent(n)      -> ""
  | White(s)       -> s
  | Comment(s)     -> "\\text{\\small(*"^s^"*)}"
  | Sep(s)         -> texify s

let rec munges ls = (* munge a list of lines *)
  match ls with
    (l::[]) -> munge l
  | (l::ls) -> munge l^"\\\\\\relax\n"^munges ls
  | []      -> ""

and munge xs = (* munge a line of tokens *)
  match xs with
    (x::xs) -> mtok x^munge xs
  | []      -> ""

and munget s = (* munge a string *)
  s

and mungelab s = (* munge the label *)
  let rec go xs =
    match xs with
      (Ident("--",_) :: xs) -> go1 xs []
    | (Indent(_) :: xs)     -> go xs
    | _                     -> raise BadLabel
  and go1 xs ys =
    match xs with
      (Ident("-->",_) :: xs) -> munge (List.rev ys)
    | (x :: xs)              -> go1 xs (x::ys)
    | _                      -> raise BadLabel
  in
  "\\inp{"^go s^"}"

let latex_rule (Rule(v,n,cat,desc,lhs,lab,rhs,side,comm)) =
  print_string ("\\rrule"^if side == [] then "n" else "c"
                         ^match comm with Some _ -> "c" | None -> "n");
  print_string ("{"^texify n^"}{"^texify cat^"}");
  print_string ("{"^(match desc with Some d -> texify d | None -> "")^"}\n");
  print_string ("{"^munges lhs^"}\n");
  print_string ("{"^mungelab lab^"}\n");
  print_string ("{"^munges rhs^"}\n");
  print_string ("{"^munges side^"}\n");
  print_string "{";
  (match comm with
     Some c -> print_string (munget c)
   | None   -> ());
  print_string "}\n\n"

let latex_render () =
  ignore (parse_rules_and_process latex_rule tokstream)

let _ =
  latex_render ()


