(* holdoc_munge.ml -- process HOL LTS or TeX or HOL into LaTeX code (library) *)
(* Keith Wansbrough 2001 *)

(* TO DO list now moved to holdoc-guide.txt, wish list section. *)

open Hollex
open Holdoc_init

exception Trailing (* there is trailing info in the file *)
exception BadLabel
exception BadDirective (* ill-positioned directive *)
exception BadArg of string (* problem parsing arg of curried fun *)

(* ------------------------------------------------------------ *)
(* Useful helpers                                               *)
(* ------------------------------------------------------------ *)

let isIndent t =
  match t with
    Indent(n) -> true
  | _         -> false

let isDirEnd t =
  match t with
    DirEnd    -> true
  | _         -> false

let isTeXNormal t =
  match t with
    TeXNormal(_) -> true
  | _            -> false

let gensymcnt = ref 0

let debug_print s =
  let n = !gensymcnt
  in
  gensymcnt := n + 1

(* ------------------------------------------------------------ *)
(* Parsers                                                      *)
(* ------------------------------------------------------------ *)

let rec parse_line = parser  (* parse a line *)
    [< 'Indent(n); e = parse_line1 >] -> Indent(n) :: e

and parse_line1 = parser
    [< 't when not (isIndent t) ; e = parse_line1 >] -> t :: e
  | [<>]                                             -> []

and parse_line0 = parser  (* parse a line; don't care if it starts with indent;
                                 process directives *)
    [< 'Indent(n); e = parse_line01 >] -> Indent(n) :: e
  | [<             e = parse_line01 >] -> e

and parse_line01 = parser
    [< 'DirBlk(n,ts) when (ignore (dir_proc n ts); true)
                     ; e = parse_line01 >] -> e
  | [< 't when not (isIndent t) && t <> Backtick
          ; e = parse_line01 >]            -> t :: e
  | [<>]                                   -> []

and parse_lineT = parser  (* parse a chunk of TeX or HOL; process directives *)
    [< 'TeXNormal(s) >] -> [TeXNormal(s)]
  | [< ts = parse_lineT1 >] -> ts

and parse_lineT1 = parser
    [< 'DirBlk(n,ts) when (ignore (dir_proc n ts); true)
                                   ; ts' = parse_lineT1 >] -> DirBlk(n,ts) :: ts'
  | [< 't when not (isTeXNormal t) ; ts  = parse_lineT1 >] -> t :: ts
  | [<>]                                                   -> []

and parse_chunk = parser (* parse a chunk delimited by a blank line *)
    [< 'Indent(n); c = parse_chunk1 n >] -> c

and parse_chunk1 n = parser
    [< 't when not (isIndent t) ; e = parse_line1 ;
       c = parse_chunk >] -> (Indent(n) :: t :: e) :: c
  | [<>]                  -> []

and parse_longchunk = parser (* parse a chunk delimited by two blank lines *)
    [< 'Indent(n1); c = parse_longchunk0 n1 >] -> c

and parse_longchunk0 n1 = parser
    [< 'Indent(n2); c = parse_longchunk1 n1 n2 >] -> c
  | [< e = parse_line1 ; c = parse_longchunk   >] -> (Indent(n1) :: e) :: c

and parse_longchunk1 n1 n2 = parser
    [< 't when not (isIndent t) ; e = parse_line1 ;
       c = parse_longchunk >] -> [Indent(n1)] :: (Indent(n2) :: t :: e) :: c
  | [<>]                  -> []

and parse_wholechunk = parser (* parse a chunk delimited by a closing backtick *)
    [< 'Backtick >]                                 -> []
  | [< 't; e = parse_line0; c = parse_wholechunk >] -> (t :: e) :: c
  | [<>]                                            -> []

and optcomm = parser
    [< 'Comment(c) >]                  -> Some [Comment(c)]
  | [< 'HolStartTeX; ts = parse_tex >] -> Some (HolStartTeX :: ts)
  | [<>]                               -> None

and parse_tex = parser
    [< 'HolEndTeX >]                                     -> [HolEndTeX]
  | [< 'TeXStartHol; ts = parse_hol;  ts' = parse_tex >] -> TeXStartHol :: ts @ ts'
  | [< 'TeXStartHol0; ts = parse_hol; ts' = parse_tex >] -> TeXStartHol :: ts @ ts'
  | [< 'TeXNormal(s);                 ts' = parse_tex >] -> TeXNormal(s) :: ts'

and parse_hol = parser
    [< 'TeXEndHol >]                                    -> [TeXEndHol]
  | [< 'TeXEndHol0 >]                                   -> [TeXEndHol0]
  | [< 'HolStartTeX; ts = parse_tex; ts' = parse_hol >] -> HolStartTeX :: ts @ ts'
  | [< 't;                           ts' = parse_hol >] -> t :: ts'

and sp = parser
    [< 'White(s)                  ; s1 = sp >] -> White(s)     :: s1
  | [< 'Comment(c)                ; s1 = sp >] -> Comment(c)   :: s1
  | [<>]                                   -> []

and wopt = parser
    [< 'White(s)  ; s1 = wopt >] -> White(s)   :: s1
  | [<>]                         -> []

and ids_nocomm = parser
    [< 'Ident(s,true) ; ss = ids_nocomm >] -> s :: ss
  | [< 'White(_)      ; ss = ids_nocomm >] -> ss
  | [<>]                                   -> []

and sp' = parser
    [< 'White(s)                  ; s1 = sp' >] -> White(s)     :: s1
  | [< 'Indent(n)                 ; s1 = sp' >] -> Indent(n)    :: s1
  | [< 'Comment(c)                ; s1 = sp' >] -> Comment(c)   :: s1
  | [<>]                                    -> []

and optind = parser
    [< 'Indent(n) ; is = optind >] -> Indent(n) :: is
  | [<>]                           -> []

and dir_var_vars ts =
  let rec go ts =
    match ts with
      (White(_)::ts)   -> go ts
    | (Comment(_)::ts) -> go ts
    | (Ident(s,_)::ts) -> s :: go ts
    | (_::ts)          -> raise BadDirective
    | []               -> []
  in
  go ts


(* ------------------------------------------------------------ *)
(* Now for the pretty-printing                                  *)
(* ------------------------------------------------------------ *)

(* converting a string to a TeX-printable form (assuming math mode in some cases) *)

let texify_list =
  [('_', "\\_")
  ;('~', "\\neg{}")
  ;('$', "\\$")
  ;('%', "\\%")
  ;('&', "\\&")
  ;('\\', "\\backslash{}")
  ;('^', "\\hat{\\phantom{x}}")
  ;('{', "\\{")
  ;('}', "\\}")
  ;('#', "\\#")
  ]

let texify_text_list =
  [('_', "\\textunderscore{}")
  ;('~', "\\textasciitilde{}")
  ;('$', "\\$")
  ;('%', "\\%")
  ;('&', "\\&")
  ;('\\', "\\textbackslash{}")
  ;('^', "\\textasciicircum{}")
  ;('{', "\\{")
  ;('}', "\\}")
  ;('#', "\\#")
  ;('<', "\\textless{}")  (* {} to work around a bug in LaTeX / fontenc: \textless\textless == \textguillemotleft  (!!!) *)
  ;('>', "\\textgreater{}")  (* {} to work around a bug in LaTeX / fontenc *)
  ]

let texify_command s =
  let f s = String.make 1 (char_of_int
                             (int_of_string
                                (Str.matched_string s)
                                + int_of_char 'A' - 1))
  in
  "\\" ^ Str.global_replace    (Str.regexp "[^A-Za-z0-9]") "X"
        (Str.global_substitute (Str.regexp "[0-9]+"      )  f
                               s)


let sepBy sep ss =
  let rec go ss =
    match ss with
      []      -> [""]
    | [s]     -> [s]
    | (s::ss) -> s::sep::go ss
  in
  String.concat "" (go ss)

let dotexify tlist =
  let re = Str.regexp (sepBy "\\|" (List.map (function (c,_) -> Str.quote (String.make 1 c)) tlist))
  in
  let go s =
    match s with
      Str.Text(s)  -> s
    | Str.Delim(s) -> List.assoc (String.get s 0) tlist
  in
  function s ->
    String.concat "" (List.map go (Str.full_split re s))

let texify = dotexify texify_list

let texify_text = dotexify texify_text_list

let texifys sep ss =
  sepBy sep (List.map texify ss)


(* recognisers for various syntactic categories *)

let is_rule s =
  Str.string_match
     (Str.regexp ".*_[0-9]+")
     s
     0

let is_type s = List.mem s !(!curmodals.tYPE_LIST)

let is_con s = List.mem s !(!curmodals.cON_LIST)

let is_field s = List.mem s !(!curmodals.fIELD_LIST)

let is_lib s = List.mem s !(!curmodals.lIB_LIST) (* lib not constructor, as special case *)

let is_aux s = List.mem s !(!curmodals.aUX_LIST)

let is_aux_infix s = List.mem s !(!curmodals.aUX_INFIX_LIST)

let is_var_prefix s = List.mem s !(!curmodals.vAR_PREFIX_LIST)

let is_curried s =
  try Some (List.assoc s !(!curmodals.hOL_CURRIED_ALIST))
  with Not_found -> None

let var_prefix s =
  let _ = (Str.search_forward
             (Str.regexp "\([0-9]*\)\([']*\)$")
             s
             0 ) in
  Str.string_before s (Str.match_beginning ())

(* is prefixed variable *)
let is_pref_var s =
  is_var_prefix (var_prefix s)

(* is known or prefixed variable *)
let is_var v s = (* v is a list of universally-quantified rule variables *)
  List.mem s v
    || is_pref_var s

let is_num s =
  Str.string_match (Str.regexp "[0-9]+") s 0

let do_sub s =
  (* return texified body (will be wrapped in typestyle)
     and texified suffix (will be appended) *)
  let _ = (Str.search_forward
             (Str.regexp "\([0-9]*\)\([']*\)$")
             s
             0 ) in
  if "" <> (Str.matched_group 1 s) then
    (texify (Str.string_before s (Str.match_beginning ())),
     "_{"^Str.matched_group 1 s^"}"^Str.matched_group 2 s)
  else
    (texify s,"")

let is_holop s = List.mem s !(!curmodals.hOL_OP_LIST)

(* translations for symbols and particular identifiers; these take precedence over is_foo *)

(* dump an unrecognised string to stderr *)
let write_unseen_string s = prerr_endline ("  \"" ^ s ^ "\"  ; ")

(* dump a warning to stderr *)
let write_warning s = prerr_endline ("WARNING: " ^ s ^ ".")

(* Now use all the above in munging tokens, lists of tokens, etc *)

let mident v s = (* munge alphanumeric identifier *)
(*  "\\tsvar{"^texify s^"}" *)
  try List.assoc s !(!curmodals.hOL_ID_ALIST)
  with Not_found ->
    if (is_num s) then texify s else
    let (c,sub)  = if (is_rule s)        then ("tsrule"    ,false) else
                   if (is_con s)         then ("tscon"     ,false) else
                   if (is_aux s)         then ("tsaux"     ,false) else
                   if (is_aux_infix s)   then ("tsauxinfix",false) else
                   if (is_lib s)         then ("tslib"     ,true ) else
                   if (is_field s)     (* treat as var, because name often shared *)
                      || (is_var v s)    then ("tsvar"     ,!(!curmodals.sMART_PREFIX)
                                                            || is_pref_var s) else
                                              (* if smart, always do foo1 -> foo_1;
                                                 otherwise, only if foo is specified as a prefix *)
                     if (is_holop s)     then ("tsholop"   ,false) else
                   if (is_type s)        then ("tstype"    ,false) else
                   (write_unseen_string s;    ("tsunknown" ,false)) in
    if sub then
      let (sb,ss) = do_sub s in
      "\\"^c^"{"^sb^"}"^ss
    else
      "\\"^c^"{"^texify s^"}"

  (* would be good to check is_* for overlaps *)

let msym v s = (* munge symbolic identifier *)
   try List.assoc s !(!curmodals.hOL_SYM_ALIST)
   with Not_found -> texify s

let mindent n = (* munge an indentation of level n *)
  let rec ntimes n x =
    if n <= 0 then
      []
    else
      x :: ntimes (n-1) x in
  let m = (n-5) / 2 in
  "{}\\\\{}\n" ^ String.concat "" (ntimes m "\\quad") ^ " "

let mdir v n ts = (* munge a directive *)
  let rec go ts =
    match ts with
      (White(_)::ts)   -> go ts
    | (Indent(_)::ts)  -> go ts
    | (Comment(_)::ts) -> go ts
    | (Ident(s,_)::ts) -> s
    | (t::ts)          -> prerr_endline ("Unexpected token in arg of "^n^": "^render_token t);
                          raise BadDirective
    | []               -> prerr_endline ("Missing arg in "^n);
                          raise BadDirective
  in
  match n with
    "SHOWRULE" -> "\\showrule{"^texify_command (go ts)^"}%"  (* NB: don't put TeX after a showrule! *)
  | _          -> ""

let balanced = [ ("(",")"); ("[","]"); ("{","}")]

let rec readbal ds ts tss cf ml = (* read a balanced arg; cf=true ==> level 1 commas to }{ and remove level 1 parens; ml=true ==> allow multi-line *)
  let rec bal ps ds ts tss =
    let n = List.length ps
    in
    match ts with
      (Sep(s)::ts) when List.mem_assoc s balanced  (* open *)
                     -> let ds' = if n=0 && cf
                                  then ds
                                  else (Sep(s)::ds)
                        in
                        bal (List.assoc s balanced::ps) ds' ts tss
    | (Sep(s)::ts) when n>0 && s = List.hd ps      (* close *)
                     -> let ds' = if n=1 && cf
                                  then ds
                                  else Sep(s)::ds
                        in
                        if n=1
                        then (List.rev ds',ts,tss)
                        else bal (List.tl ps) ds' ts tss
    | (Sep(",")::ts) -> if n=1 && cf
                        then bal ps (TeXNormal("}{")::ds) ts tss
                        else bal ps (Sep(",")       ::ds) ts tss
    | (Indent(_)::ts) when n=1 && ml  (* strip first-level indentation of multiline *)
                     -> bal ps ds ts tss
    | (t::ts)        -> bal ps (t::ds) ts tss
    | []             -> (match tss with
                           (ts::tss) when ml -> bal ps (TeXNormal("\\\\\n")::ds) ts tss
                         | _                 -> raise (BadArg "1"))
  in
  bal [] ds ts tss

let rec readarg cf ml ts tss = (* read a single arg: spaces then (id.id.id or matched-paren string) *)
  let rec sp ts tss =
    match (ts,tss) with
      (White(_)::ts,_)     -> sp ts tss
    | (Indent(_)::ts,_)    -> sp ts tss
    | ([],ts::tss) when ml -> sp ts tss
    | _                    -> (ts,tss)
  in
  let rec dotted ds ts tss =
    match ts with
      (Sep(".")::Ident(s,true)::ts) -> dotted (Ident(s,true)::Sep(".")::ds) ts tss
    | (Str(_)::_)                   -> raise (BadArg "2")
    | (Ident(_,_)::_)               -> raise (BadArg "3")
    | _                             -> (List.rev ds,ts,tss)
  in
  match sp ts tss with
    (Ident(s,_)::ts,tss)    -> dotted [Ident(s,true)] ts tss
  | (Sep(s)::ts,tss) when List.mem_assoc s balanced
                            -> readbal [] (Sep(s)::ts) tss cf ml (* commas to add extra args? *)
  | (t::ts,tss)             -> raise (BadArg ("4: "^render_token t))
  | ([],_)                  -> raise (BadArg "5")


let rec mtok v t =
  if !eCHO then
    match t with
      Ident(s,true)  -> mident v s
    | Ident(s,false) -> msym v s
    | Indent(n)      -> if !(!curmodals.iNDENT) then mindent n else "\n" (* only render if desired *)
    | White(s)       -> s
    | Comment(s)     -> (if String.contains s '\n' then  (* anything split over a line must be long *)
                           "\\tslongcomm{"
                         else
                           "\\tscomm{")
                        ^texify_text s^"}"
    | Str(s)         -> "\\text{``"^texify_text s^"''}"
    | DirBlk(n,ts)   -> mdir v n ts
    | DirBeg         -> raise BadDirective
    | DirEnd         -> raise BadDirective
    | Sep(s)         -> texify s
    | Backtick       -> "\\texttt{`}"
    | DBacktick      -> "\\texttt{``}"
    | TeXStartHol    -> !hOLDELIMOPEN   (* "$" *)
    | TeXStartHol0   -> ""
    | TeXEndHol      -> !hOLDELIMCLOSE  (* "$" *)
    | TeXEndHol0     -> ""
    | TeXNormal(s)   -> s
    | HolStartTeX    -> "\\tsholcomm{"
    | HolEndTeX      -> "}"
  else
    ""


and mcurry x c n cf ml v xs xss = (* munge n arguments of curried function c;
                             return string and remainder;
                             strip outer parens and turn commas to }{ if b *)
  let wrap ys = "{"^munge v ys []^"}"
  in
  let rec go n args ts tss =
    if n <= 0 then (c^String.concat "" (List.map wrap (List.rev args)),ts,tss)
    else match readarg cf ml ts tss with
           (ds,ts,tss) -> go (n-1) (ds::args) ts tss
  in
  try
    go n [] xs xss
  with
    BadArg(s) -> (* abort curry parse; do it uncurried *)
              let w = "curry parse failed: "^mtok v x^" ==> "^c
              in
              write_warning (w^" "^s);
              ("\n% WARNING: "^w^" "^s^"\n"^mtok v x^"%\n%\n",xs,xss)

and munges v ls = (* munge a list of lines *)
  match ls with
  | (l::ls) -> munge v l ls
  | []      -> ""

and munge v xs xss = (* munge the first line of tokens *)
  match xs with
    (Ident(s,b)::xs)    -> (match is_curried s with
                              Some (c,n,cf,ml)
                                   -> let (s,xs',xss') = mcurry (Ident(s,b)) c n cf ml v xs xss
                                      in
                                      s^munge v xs' xss'
                            | None -> mtok v (Ident(s,b))^munge v xs xss)
  | (x::xs)             -> mtok v x^munge v xs xss
  | []                  -> (match xss with
                              [] -> ""
                            | (xs::xss) -> munge v xs xss)

and mungelab v s = (* munge the label *)
  let rec go xs =
    match xs with
      (Ident("--",_) :: xs) -> go1 xs []
    | (Ident("---",_) :: xs)-> go1 xs []
    | (Indent(_) :: xs)     -> go xs
    | _                     -> raise BadLabel
  and go1 xs ys =
    match xs with
      (Ident("-->",_) :: xs) -> munge v (List.rev ys) []
    | (Ident("--->",_) :: xs)-> munge v (List.rev ys) []
    | (Ident("--=>",_) :: xs)-> munge v (List.rev ys) []
    | (x :: xs)              -> go1 xs (x::ys)
    | _                      -> raise BadLabel
  in
  "\\inp{"^go s^"}"


(* ------------------------------------------------------------ *)
(* Rule-specific stuff                                          *)
(* ------------------------------------------------------------ *)

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

(* the rule type *)

type rule =
    Rule of string list * string * string list * token list option (* v, n, cat, desc, *)
        * token list list * token list * token list list (* lhs, lab, rhs, *)
        * token list list * token list option (* side, comm *)
  | Definition of token list list

(* debugging rule printer *)

let print_tokenline toks =
    let f t = print_string ((render_token t)^" ")
    in
(* DEBUG: print_string "TOKEN LINE: "; *)
    ignore (List.map f toks);
    print_newline()

let print_rule ruleordefn =
  match ruleordefn with
    Rule(v,n,cat,desc,lhs,lab,rhs,side,comm) ->
      print_string ("Rule "^n^" (");
      ignore (List.map (function s -> print_string (s^" ")) cat);
      (match desc with
         Some d -> print_string " ";
                   print_tokenline d
       | None   -> ());
      print_string ")\n";
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
      (match comm with
         Some c -> print_string "Comments:\n";
                   print_tokenline c;
                   print_newline()
      |  None   -> ());
      print_newline()
  | Definition(e) ->
      print_string "Definition:\n";
      ignore (List.map print_tokenline e);
      print_newline()

(* parsing a rule *)

let rec parse_rule = parser
    [< 'Sep("("); _ = sp; r1 = parse_rule1 >] -> r1
  | [<>] -> raise (Stream.Error("rule begin: `('"));
and parse_rule1 = parser
    [< 'Ident("!",_); v = rule_vars; _ = sp; 'Sep(".") ?? ".";
       _ = sp';
       (n,cat,desc) = rule_name;
       l_lab_r = parse_chunk;
       'Indent(_);
       _ = sp'; 'Ident("<==",_) ?? n^": <=="; _ = sp;
       'Indent(_);
       side = parse_longchunk;
       'Indent(_); _ = optind;
       comm = optcomm;
       _ = optind;
       _ = sp; 'Sep(")") ?? n^": rule end: `)'"; _ = sp >]
      -> let rec isLab ts =
            match ts with
              (Indent(_)     :: ts) -> isLab ts
            | (White(_)      :: ts) -> isLab ts
            | (Ident("--",_) :: _ ) -> true
            | (Ident("---",_):: _ ) -> true
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

and parse_definition = parser
    [< e = parse_wholechunk >] -> Definition(e)
  | [<>] -> raise (Stream.Error("Couldn't parse definition!"));

and rule_vars = parser
    [< 'White(_)                  ; r = rule_vars >] -> r
  | [< 'Indent(_)                 ; r = rule_vars >] -> r
  | [< 'Comment(_)                ; r = rule_vars >] -> r
  | [< 'DirBlk("VARS",ts)         ; r = rule_vars >] -> dir_var_vars ts @ r
  | [< 'DirBlk(n,ts) when (dir_proc n ts; true) (* cheat: make it happen right now *)
                                  ; r = rule_vars >] -> r
  | [< 'Ident(s,_)                ; r = rule_vars >] -> s :: r
  | [<>]                                         -> []

and rule_name = parser
    [< 'Ident(n,_); _ = sp; 'Ident("/*",_) ?? "/*"; _ = sp; cat = ids_nocomm ?? "category"; _ = wopt;
       desc = optcomm; _ = sp; 'Ident("*/",_) ?? "*/"; _ = sp >]
      -> debug_print ("GOT "^n^"\n"); (n,cat,desc)
  | [<>] -> raise (Stream.Error("can't find rule name"));


and parse_rules_and_process p = parser
    [< 'Ident("Net_Hol_reln",_); _ = sp'; rs = parse_rules_ap0 p; rest = parse_rules_and_process p >] -> rs @ rest
  | [< 'Ident("Define",_); _ = sp'; r = parse_definition_ap0 p; rs = parse_rules_and_process p >] -> r :: rs
  | [< 'DirBlk(n,ts) when (dir_proc n ts; true) (* cheat: make it happen right now *)
                               ; rs = parse_rules_and_process p  >] -> rs
  | [< '_                      ; rs = parse_rules_and_process p  >] -> rs
  | [<>] -> []
and parse_rules_ap0 p = parser
    [< 'Backtick; _ = sp'; rs = parse_rules_ap1 p >] -> rs
  | [< rs = parse_rules_and_process p             >] -> rs
and parse_rules_ap1 p = parser
    [< 'Sep("("); _ = sp; r = (function ts -> p (parse_rule1 ts)); _ = sp';
       rs = parse_rules_ap2 p >] -> r :: rs
  | [<>]                         -> []
and parse_rules_ap2 p = parser
    [< 'Ident("/\\",_); _ = sp';
       rs = parse_rules_ap1 p >] -> rs
  | [< 'Backtick >]              -> []
  | [<>]                         -> raise (Stream.Error("expected /\\ or `"))
and parse_definition_ap0 p = parser
    [< 'Backtick; _ = sp'; r = (function ts -> p (parse_definition ts)) >] -> r
  | [<>] -> raise (Stream.Error("expected ` after Define"))


(* get a list of the potential variables in a rule, ie, all idents
   that are bound somewhere *)

(* note that we can't find the binders in a set comprehension, *very*
   annoyingly.  See this from Michael:

   Subject: Typesetting HOL
   From: Michael Norrish <Michael.Norrish@cl.cam.ac.uk>
   Date: Thu, 5 Jul 2001 12:59:09 +0100
   To: Keith Wansbrough <Keith.Wansbrough@cl.cam.ac.uk>

   [..]
   > * in set comprehension notation { foo | bar }, how can I determine the
   > set of bound variables?

   You can't.  It's a long-standing problem with the syntax.  The parser
   resolves the ambiguity by taking the intersection of variables on the
   left and right-hand sides, unless there are none on one or other side,
   when it just takes the free-vars on the other side to all be bound.
   It's a hideous hack.

   Michael.

*)

let hol_binders =
  [ "!"
  ; "?"
  ; "?!"
  ; "@"
  ; "\\"
  ]

let potential_vars_line ts =
    let rec pot_l ts =       (* binders in a line *)
      match ts with
        (Ident(s,_)::ts) -> if List.mem s hol_binders then
                              bdrs ts
                            else
                              pot_l ts
      | (_::ts)          -> pot_l ts
      | []               -> []
    and bdrs ts =        (* we've hit a binder; read vars until separator *)
      match ts with
        (Ident(s,_)::ts)       -> s :: bdrs ts
      | (DirBlk("VARS",s)::ts) -> dir_var_vars s @ bdrs ts
      | (Sep(s)::ts)           -> pot_l ts
      | (_::ts)                -> bdrs ts
      | []                     -> []
    in
    pot_l ts

let rec pot_s ls =       (* binders in lines *)
    match ls with
      (l::ls) -> pot_l l @ pot_s ls
    | []      -> []
and pot_l ts = potential_vars_line ts;;

let potential_vars ruleordefn =
  match ruleordefn with
    Rule(v,n,cat,desc,lhs,lab,rhs,side,comm) ->
      v              (* bound at top *)
                     (* bound in each bit... *)
      @ (match desc with Some c -> pot_l c | None -> [])
      @ pot_s lhs
      @ pot_l lab
      @ pot_s rhs
      @ pot_s side
      @ (match comm with Some c -> pot_l c | None -> [])
  | Definition(e) ->
      pot_s e

(* choose names for definitions *)

let rec roman n =
  let codes = [(1000,"m")
              ;(900,"cm")
              ;(500,"d")
              ;(400,"cd")
              ;(100,"c")
              ;(90,"xc")
              ;(50,"l")
              ;(40,"xl")
              ;(10,"x")
              ;(9,"ix")
              ;(5,"v")
              ;(4,"iv")
              ;(1,"i")
              ]
  in
  let rec first n cs =
    match cs with
      ((m,s)::cs) -> if n >= m then Some(m,s) else first n cs
    | []          -> None
  in
  match first n codes with
    Some(m,s) -> s ^ roman (n-m)
  | None      -> if n = 0 then "" else raise Not_found;;

let defctr = ref (1:int);;
let gendefname () = let n = !defctr in defctr := n+1; "\\defn" ^ roman n;;

let getname ls =
  let rec go ts =
    match ts with
      (Ident(s,_) as t::_) -> Some t
    | (_::ts)              -> go ts
    | []                   -> None
  in
  match ls with
    (l::_) -> go l
  | []     -> None

(* output (munge) a whole rule *)

let latex_rule ruleordefn =
  match ruleordefn with
    Rule(v,n,cat,desc,lhs,lab,rhs,side,comm) as r ->
      (* DEBUG:  let _ = print_rule r in *)
      let pvs      = potential_vars r
      in
      let texname  = texify_command n
      in
      print_string ("\\newcommand{"^texname^"}{\\rrule"^(if side = [] then "n" else "c")
                             ^(match comm with Some _ -> "c" | None -> "n"));
      print_string ("{"^texify n^"}{"^texifys " " cat^"}");
      print_string ("{"^(match desc with Some d -> munge pvs d [] | None -> "")^"}\n");
      print_string ("{"^munges pvs lhs^"}\n");
      print_string ("{"^mungelab pvs lab^"}\n");
      print_string ("{"^munges pvs rhs^"}\n");
      print_string ("{"^munges pvs side^"}\n");
      print_string "{";
      (match comm with
         Some c -> print_string (munge pvs c [])
       | None   -> ());
      print_string "}}\n\n";
      texname
  | Definition(e) ->
      let pvs      = pot_s e
      in
      let namepart = match getname e with
                       Some t -> mtok pvs t
                     | None   -> "{}"
      in
      let texname = gendefname()
      in
      print_string ("\\newcommand{"^texname^"}{\\ddefn{"^namepart^"}{"^munges pvs e^"}\n}\n\n");
      texname

(* ------------------------------------------------------------ *)
(* renderer entry points                                        *)
(* ------------------------------------------------------------ *)

(* get first filename or stdin as input channel *)
let get_inchan () =
  let filename = ref None in
  let _ = Arg.parse [] (function s -> filename := Some s) "Bad argument" in
  match !filename with
    Some filename -> open_in filename
  | None -> stdin

(* render LTS (rules) from whole input stream *)
let lts_latex_render () =
  let tokstream = holtokstream (get_inchan ()) in
  let _        = print_string "%%%% AUTOGENERATED FILE (from LTS source) -- DO NOT EDIT! %%%%\n" in
  let rulecmds = parse_rules_and_process latex_rule tokstream in
  let go rn    = print_string ("\\showrule{"^rn^"}\n")
  in
  print_string "\\newcommand{\\dumpallrules}{\n";
  ignore (List.map go rulecmds);
  print_string "}\n\n";
  (match !rCSID with
     Some s -> print_string ("\\newcommand{\\rulesrcsid}{"^texify s^"}\n\n")
   | None   -> ());
  print_string "%%%% END %%%%\n"


let pvs = ref []  (* possible variable names; not used for LTS *)

(* render MNG from whole input stream *)

let mng_latex_render () =
  let tokstream = textokstream (get_inchan ()) in
  let rec go () =
    match Stream.peek tokstream with
      Some _ -> let ts = parse_lineT tokstream
                in
                print_string (munge (potential_vars_line ts) ts []);
                go ()
    | None   -> ()
  in
  (* must fix handling of VARS directives *)
  (* NB: no trailing newline - we hope the first line of source is a comment already! *)
  print_string "%%%% AUTOGENERATED FILE (from MNG source) -- DO NOT EDIT! %%%% ";
  go ()

(* render HOL from whole input stream *)

let hol_latex_render () =
  let tokstream = holtokstream (get_inchan ()) in
  let rec go () =
    match Stream.peek tokstream with
      Some _ -> let ts = parse_line0 tokstream
                in
                pvs := potential_vars_line ts @ !pvs;
                print_string ("\\holline{"^munge !pvs ts []^"}\n");
                go ()
    | None   -> ()
  in
  (* must fix handling of VARS directives *)
  print_string "%%%% AUTOGENERATED FILE (from HOL source) -- DO NOT EDIT! %%%%\n";
  go ()

(* ------------------------------------------------------------ *)
(* end                                                          *)
(* ------------------------------------------------------------ *)
