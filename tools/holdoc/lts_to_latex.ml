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


(* debugging rule printer *)

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



(* now for the pretty-printing *)

(* converting a string to a TeX-printable form (assuming math mode in some cases) *)

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


(* recognisers for various syntactic categories *)

let is_rule s = try 
                  (String.index s '.' ) <> (String.length s) -1
                with
                  Not_found -> false

  (* could be autogenerated from Net_typesScript.sml etc *)
let is_type s = List.mem s 
  [ "port"
  ; "ip"
  ; "ipBody"
  ; "msg"
  ; "ifid"
  ; "netmask"
  ; "ifd"
  ; "fd"
  ; "error"
  ; "err"
  ; "sockopt"
  ; "TLang_type"
  ; "TLang"
  ; "hostThreadState"
  ; "flags"
  ; "socket"
  ; "host"
  (* and from Net_hostLTSScript.sml *)
  ; "LIB_interface"
  ; "Lhost0"
  ; "rule_ids"
  ; "rule_cats"
  ] 

  (* could be autogenerated from Net_typesScript.sml etc *)
let is_con s = List.mem s 
  [ "Port"
  ; "ip"
  ; "UDP"
  ; "ICMP_HOST_UNREACH"
  ; "ICMP_PORT_UNREACH"
  ; "LO"
  ; "ETH"
  ; "NETMASK"
  ; "FD"
  ; "EACCES"
  ; "EADDRINUSE"
  ; "EADDRNOTAVAIL"
  ; "EAGAIN"
  ; "EBADF"
  ; "ECONNREFUSED"
  ; "EHOSTUNREACH"
  ; "EINTR"
  ; "EINVAL"
  ; "EMFILE"
  ; "EMSGSIZE"
  ; "ENFILE"
  ; "ENOBUFS"
  ; "ENOMEM"
  ; "ENOTCONN"
  ; "ENOTSOCK"
  ; "OK"
  ; "FAIL"
  ; "SO_BSDCOMPAT"
  ; "SO_REUSEADDR"
  ; "TLty_int"
  ; "TLty_bool"
  ; "TLty_string"
  ; "TLty_one"
  ; "TLty_pair"
  ; "TLty_list"
  ; "TLty_lift"
  ; "TLty_err"
  ; "TLty_fd"
  ; "TLty_ip"
  ; "TLty_port"
  ; "TLty_error"
  ; "TLty_netmask"
  ; "TLty_ifid"
  ; "TLty_sockopt"
  ; "TL_int"
  ; "TL_bool"
  ; "TL_string"
  ; "TL_one"
  ; "TL_pair"
  ; "TL_list"
  ; "TL_option"
  ; "TL_err"
  ; "TL_fd"
  ; "TL_ip"
  ; "TL_port"
  ; "TL_error"
  ; "TL_netmask"
  ; "TL_ifid"
  ; "TL_sockopt"
  ; "Run"
  ; "Term"
  ; "Ret"
  ; "Sendto2"
  ; "Recvfrom2"
  ; "Select2"
  ; "Print2"
  ; "Flags"  (* not a real constructor, but an xDefined one; etc *)
  ; "Sock"
  (* and from Net_hostLTSScript.sml *)
  ; "Lh_call"
  ; "Lh_return"
  ; "Lh_sendmsg"
  ; "Lh_recvmsg"
  ; "Lh_console"
  ; "Lh_tau"
  (* rule_ids and rule_cats omitted *)
]

let is_field s = List.mem s
  [ "src"
  ; "dest"
  ; "body"
  ; "ifid"
  ; "ipset"
  ; "primary"
  ; "netmask"
  ; "bsdcompat"
  ; "reuseaddr"
  ; "fd"
  ; "is1"
  ; "ps1"
  ; "is2"
  ; "ps2"
  ; "es"
  ; "f"
  ; "mq"
  ; "ifds"
  ; "t"
  ; "s"
  ; "oq"
  ; "oqf"
  ] 

let is_lib s = List.mem s  (* lib not constructor, as special case *)
  [ "socket"
  ; "bind"
  ; "connect"
  ; "disconnect"
  ; "getsockname"
  ; "getpeername"
  ; "sendto"
  ; "recvfrom"
  ; "geterr"
  ; "getsockopt"
  ; "setsockopt"
  ; "close"
  ; "select"
  ; "port_of_int"
  ; "ip_of_string"
  ; "getifaddrs"
  ; "print_endline_flush"
  ; "exit"
  ]

let is_aux s = List.mem s  (* based on Net_auxfnsScript.sml *)
  [ "enqueue"
  ; "outroute"
  ; "dosend"
  ; "unused"
  ; "ephemeral"
  ; "ephemeralErrors"
  ; "privileged"
  ; "socklist_context"
  ; "scs1"
  ; "scs2"
  ; "F_context"
  ; "fc_sc"
  ; "fc_oq"
  ; "fc_oqf"
  (* omit SC_unused, FC_unused as overloaded on unused *)
  ; "autobind"
  ; "socks"
  (* and Net_oksScript.sml *)
  ; "netmask_ok"
  ; "num_of_mask"
  ; "mask"
  ; "LOOPBACK"
  ; "MULTICAST"
  ; "BADCLASS"
  ; "ZERONET"
  ; "MARTIAN"
  ; "body_ips"
  ; "martian"
  ; "loopback"
  ; "ifd_set_ok"
  ; "UDPpayloadMax"
  ; "msg_ok"
  ; "msg_oq_ok"
  ; "socket_srcdest_ok"
  ; "socket_ok"
  ; "sockfds"
  ; "sock_with_fd"
  ; "host_ok"
  (* added by hand *)
  ; "string_size"
  ] 

let is_aux_infix s = List.mem s 
  [ "with"
  ]

let is_var_prefix s = List.mem s
  [
  ]

let is_var v s = (* v is a list of universally-quantified rule variables *)
  List.mem s v ||
  List.mem s
  [ "s'"
  ] 

(* was: (Str.string_match 
                  (Str.regexp "\([A-Za-z]+\)[0-9]*[']*")
                  s
                  0 ) &&
               (Str.match_end() = String.length s) && 
               (is_var_prefix (Str.matched_group 1 s))
 *)

  (* magic for subscripting vars; not presently used *)
let subscript_var s = 
  let _ = (Str.string_match 
             (Str.regexp "\([A-Za-z]+\)\([0-9]*\)\([']*\)")
             s
             0 ) in 
  if "" <> (Str.matched_group 2 s) then 
    ((Str.matched_group 1 s)^(Str.matched_group 3 s)^"_{"^(Str.matched_group 2 s)^"}")
  else 
    (Str.matched_group 1 s)^(Str.matched_group 3 s)

let is_holop s = List.mem s
  [ "IMAGE"
  ; "APPEND"
  ; "FILTER"
  ; "MEM"
  ; "LIST_TO_SET"
  ] 

(* translations for symbols and particular identifiers; these take precedence over is_foo *)

let holsyms =
  [ ("/\\","\\wedge ")
  ; ("\\/","\\vee ")
  ; ("<|","\\langle\\![")
  ; ("|>","]\\!\\rangle ")
  ; ("!","\\forall ")
  ; ("?","\\exists ")
  ; ("?!","\\exists!")
  ; ("==>","\\implies")
  ; ("<==","\\impliedby")
  ; ("<=","\\leq ")
  ; (">=","\\geq ")
  ; ("<>","\\neq ")
                             (* Mquotedstring *)
  ; ("->","\\totype ")
  ; ("<=>","\\iff ")
  ; (":=","\\mathop{:=}")
  ; ("::","\\mathbin{::}")
  ; ("[]","[\,]")  (* DOESN'T WORK BECAUSE NONAGGREGATING *)
  ]

let holids =
  [ ("SOME","\\mathord{\\uparrow}")
  ; ("NONE","*")
  ; ("IN","\\in ")
  ; ("INTER","\\cap ")
  ; ("UNION","\\cup ")
  ; ("EMPTY","\\emptyset ")
  ; ("one","()")
  ; ("SUBSET","\\subseteq ")
  ; ("T","\\textbf{T}")
  ; ("F","\\textbf{F}")
  ] 

(* dump an unrecognised string to stderr *)
let write_unseen_string s = prerr_endline ("  \"" ^ s ^ "\"  ; ")


(* Now use all the above in munging tokens, lists of tokens, etc *)

let mident v s = (* munge alphanumeric identifier *)
(*  "\\tsvar{"^texify s^"}" *)
  try List.assoc s holids
  with Not_found ->
    let s' = texify s and
        c  = if (is_rule s)      then "tsrule" else
             if (is_con s)       then "tscon" else
             if (is_aux s)       then "tsaux" else
             if (is_aux_infix s) then "tsauxinfix" else
(* no types:   if (is_type s)      then "tstype" else *)
             if (is_lib s)       then "tslib" else
             if (is_field s)     (* treat as var, because name often shared *)
               || (is_var v s)   then "tsvar" else
             if (is_holop s)     then "tsholop" else 
             (write_unseen_string s;  "tsunknown") in
    "\\"^c^"{"^s'^"}"

  (* would be good to check is_* for overlaps *)

let msym v s = (* munge symbolic identifier *)
   try List.assoc s holsyms
   with Not_found -> texify s

let mtok v t =
  match t with
    Ident(s,true)  -> mident v s
  | Ident(s,false) -> msym v s
  | Indent(n)      -> ""
  | White(s)       -> s
  | Comment(s)     -> "\\text{\\small(*"^s^"*)}"
  | Sep(s)         -> texify s

let rec munges v ls = (* munge a list of lines *)
  match ls with
    (l::[]) -> munge v l
  | (l::ls) -> munge v l^"{}\\\\\n{}"^munges v ls
  | []      -> ""

and munge v xs = (* munge a line of tokens *)
  match xs with
    (x::xs) -> mtok v x^munge v xs
  | []      -> ""

and munget v s = (* munge a string *)
  s

and mungelab v s = (* munge the label *)
  let rec go xs =
    match xs with
      (Ident("--",_) :: xs) -> go1 xs []
    | (Indent(_) :: xs)     -> go xs
    | _                     -> raise BadLabel
  and go1 xs ys =
    match xs with
      (Ident("-->",_) :: xs) -> munge v (List.rev ys)
    | (x :: xs)              -> go1 xs (x::ys)
    | _                      -> raise BadLabel
  in
  "\\inp{"^go s^"}"

(* munge a whole rule *)

let latex_rule (Rule(v,n,cat,desc,lhs,lab,rhs,side,comm)) =
  print_string ("\\rrule"^if side == [] then "n" else "c"
                         ^match comm with Some _ -> "c" | None -> "n");
  print_string ("{"^texify n^"}{"^texify cat^"}");
  print_string ("{"^(match desc with Some d -> texify d | None -> "")^"}\n");
  print_string ("{"^munges v lhs^"}\n");
  print_string ("{"^mungelab v lab^"}\n");
  print_string ("{"^munges v rhs^"}\n");
  print_string ("{"^munges v side^"}\n");
  print_string "{";
  (match comm with
     Some c -> print_string (munget v c)
   | None   -> ());
  print_string "}\n\n"

(* render the whole input stream *)

let latex_render () =
  ignore (parse_rules_and_process latex_rule tokstream)

(* main program *)

let _ =
  latex_render ()


