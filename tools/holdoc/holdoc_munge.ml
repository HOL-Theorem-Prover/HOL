(* holdoc_munge.ml -- process HOL LTS or TeX or HOL into LaTeX code (library) *)
(* Keith Wansbrough 2001 *)

(* TO DO:

- could autogenerate various sets used in is_foo checking.

- do quoted strings

- do indentation (taking open delimiters into account)

- all sorts of spacing issues

- do transition labels more nicely

- add spacing after (some) constructors; or if not followed by ( or separator.

- ditto for library functions

- fancy typesetting for context conditions like F_context FC

- Charter has a particularly ugly underscore, eg in print_endline_flush.

- allow empty side conditions; don't force T.

- compute binders in set comprehension somehow (see note below).

- convert ~(m.src IN MARTIAN) to m.src \notin MARTIAN.

- spacing in curried functions, eg append in delivery_loopback_udp_2,
  between first and second args.

 *)

open Hollex
open Holdoc_init

exception Trailing (* there is trailing info in the file *)
exception BadLabel
exception BadDirective (* ill-positioned directive *)

(* a useful helper *)
let isIndent t =
  match t with
    Indent(n) -> true
  | _         -> false

let isDirEnd t =
  match t with
    DirEnd    -> true
  | _         -> false

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
    Rule of string list * string * string * token list option (* v, n, cat, desc, *)
        * token list list * token list * token list list (* lhs, lab, rhs, *)
        * token list list * token list option (* side, comm *)


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

and sp' = parser
    [< 'White(s)                  ; s1 = sp' >] -> White(s)     :: s1
  | [< 'Indent(n)                 ; s1 = sp' >] -> Indent(n)    :: s1
  | [< 'Comment(c)                ; s1 = sp' >] -> Comment(c)   :: s1
  | [<>]                                    -> []

and optind = parser
    [< 'Indent(n) ; is = optind >] -> Indent(n) :: is
  | [<>]                           -> []

and dir_block = parser
    [< _ = wopt; 'Ident(n,_); ts = dir_block1 >] -> (n,ts)
and dir_block1 = parser
    [< 't when not (isDirEnd t) ; ts = dir_block1 >] -> t :: ts
  | [< 'DirEnd >]                                    -> []

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
    [< 'White(_)                  ; r = rule_vars >] -> r
  | [< 'Comment(_)                ; r = rule_vars >] -> r
  | [< 'DirBlk("VARS",ts)         ; r = rule_vars >] -> dir_var_vars ts @ r
  | [< 'DirBlk(_,_)               ; r = rule_vars >] -> r
  | [< 'Ident(s,_)                ; r = rule_vars >] -> s :: r
  | [<>]                                         -> []

and rule_name = parser
    [< 'Indent(_); 'Ident(n,_) ?? "rule name"; _ = sp; 'Ident("/*",_) ?? "/*"; _ = sp; 'Ident(cat,_) ?? "category"; _ = wopt;
       desc = optcomm; _ = sp; 'Ident("*/",_) ?? "*/"; _ = sp >]
      -> (n,cat,desc)
  | [<>] -> raise (Stream.Error("rule name on new line"));


and parse_rules_and_process p = parser
    [< 'Ident("Net_Hol_reln",_); _ = sp'; rs = parse_rules_ap0 p >] -> rs
  | [< 'DirBlk(n,ts) when (dir_proc n ts; true) (* cheat: make it happen right now *)
                               ; rs = parse_rules_and_process p  >] -> rs
  | [< '_                      ; rs = parse_rules_and_process p  >] -> rs
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

(* let's do this thing *)

(* debugging rule printer *)

let print_rule (Rule(v,n,cat,desc,lhs,lab,rhs,side,comm)) =
  print_string ("Rule "^n^" ("^cat);
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

let texify_text_list =
  [('_', "\\textunderscore ")
  ;('~', "\\textasciitilde ")
  ;('$', "\\$")
  ;('%', "\\%")
  ;('&', "\\&")
  ;('\\', "\\textbackslash ")
  ;('^', "\\textasciicircum ")
  ;('{', "\\{")
  ;('}', "\\}")
  ]

let dotexify tlist s =
  let go c =
    try List.assoc c tlist
    with Not_found -> String.make 1 c
  in
  let mapString f s =
    let rec mapS f i n s =
      if i>=n then [] else f (String.get s i) :: mapS f (i+1) n s
    in
    mapS f 0 (String.length s) s
  in
  String.concat "" (mapString go s)


let texify s = dotexify texify_list s

let texify_text s = dotexify texify_text_list s


(* recognisers for various syntactic categories *)

let is_rule s = try 
                  (String.index s '.' ) <> (String.length s) -1
                with
                  Not_found -> false

let is_type s = List.mem s !tYPE_LIST

let is_con s = List.mem s !cON_LIST

let is_field s = List.mem s !fIELD_LIST

let is_lib s = List.mem s !lIB_LIST (* lib not constructor, as special case *)

let is_aux s = List.mem s !aUX_LIST

let is_aux_infix s = List.mem s !aUX_INFIX_LIST

let is_var_prefix s = List.mem s !vAR_PREFIX_LIST

let is_var v s = (* v is a list of universally-quantified rule variables *)
  List.mem s v

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

let is_holop s = List.mem s !hOL_OP_LIST

(* translations for symbols and particular identifiers; these take precedence over is_foo *)

(* dump an unrecognised string to stderr *)
let write_unseen_string s = prerr_endline ("  \"" ^ s ^ "\"  ; ")


(* Now use all the above in munging tokens, lists of tokens, etc *)

let mident v s = (* munge alphanumeric identifier *)
(*  "\\tsvar{"^texify s^"}" *)
  try List.assoc s !hOL_ID_ALIST
  with Not_found ->
    if (is_num s) then texify s else
    let (c,sub)  = if (is_rule s)        then ("tsrule"    ,false) else
                   if (is_con s)         then ("tscon"     ,false) else
                   if (is_aux s)         then ("tsaux"     ,false) else
                   if (is_aux_infix s)   then ("tsauxinfix",false) else
(* no types:   if (is_type s)      then "tstype" else *)
                   if (is_lib s)         then ("tslib"     ,true ) else
                   if (is_field s)     (* treat as var, because name often shared *)
                      || (is_var v s)    then ("tsvar"     ,true ) else
                     if (is_holop s)     then ("tsholop"   ,false) else 
                   (write_unseen_string s;    ("tsunknown" ,false)) in
    if sub then
      let (sb,ss) = do_sub s in
      "\\"^c^"{"^sb^"}"^ss
    else
      "\\"^c^"{"^texify s^"}"

  (* would be good to check is_* for overlaps *)

let msym v s = (* munge symbolic identifier *)
   try List.assoc s !hOL_SYM_ALIST
   with Not_found -> texify s

let mindent n = (* munge an indentation of level n *)
  let rec ntimes n x =
    if n <= 0 then
      []
    else
      x :: ntimes (n-1) x in
  let m = (n-5) / 2 in
  String.concat "" (ntimes m "\\quad") ^ " "

let rec mtok v t =
  match t with
    Ident(s,true)  -> mident v s
  | Ident(s,false) -> msym v s
  | Indent(n)      -> mindent n
  | White(s)       -> s
  | Comment(s)     -> "\\tscomm{"^texify_text s^"}"
  | Str(s)         -> "\\text{``"^s^"''}"
  | DirBlk(_,_)    -> ""
  | DirBeg         -> raise BadDirective
  | DirEnd         -> raise BadDirective
  | Sep(s)         -> texify s
  | Backtick       -> "\\texttt{`}"
  | DBacktick      -> "\\texttt{``}"
  | TeXStartHol    -> "$"
  | TeXStartHol0   -> ""
  | TeXEndHol      -> "$"
  | TeXEndHol0     -> ""
  | TeXNormal(s)   -> s
  | HolStartTeX    -> "\\tscomm{"
  | HolEndTeX      -> "}"

and munges v ls = (* munge a list of lines *)
  match ls with
    (l::[]) -> munge v l
  | (l::ls) -> munge v l^"{}\\\\\n{}"^munges v ls
  | []      -> ""

and munge v xs = (* munge a line of tokens *)
  match xs with
    (x::xs) -> mtok v x^munge v xs
  | []      -> ""

and munget v s = (* munge a string *)
  let hack_re1 = Str.regexp "\\[\\[" in
  let hack_re2 = Str.regexp "\\]\\]" in
  Str.global_replace hack_re2 "$" (Str.global_replace hack_re1 "$" s)

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

let potential_vars (Rule(v,n,cat,desc,lhs,lab,rhs,side,comm)) =
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
      | []                     -> [] in
    let rec pot_s ls =       (* binders in lines *)
      match ls with
        (l::ls) -> pot_l l @ pot_s ls
      | []      -> [] in
    v              (* bound at top *)
                   (* bound in each bit... *)
    @ (match desc with Some c -> pot_l c | None -> [])
    @ pot_s lhs
    @ pot_l lab
    @ pot_s rhs
    @ pot_s side
    @ (match comm with Some c -> pot_l c | None -> [])

(* munge a whole rule *)

let latex_rule (Rule(v,n,cat,desc,lhs,lab,rhs,side,comm) as r) =
  let pvs = potential_vars r in
  print_string ("\\showrule{\\rrule"^if side == [] then "n" else "c"
                         ^match comm with Some _ -> "c" | None -> "n");
  print_string ("{"^texify n^"}{"^texify cat^"}");
  print_string ("{"^(match desc with Some d -> munge pvs d | None -> "")^"}\n");
  print_string ("{"^munges pvs lhs^"}\n");
  print_string ("{"^mungelab pvs lab^"}\n");
  print_string ("{"^munges pvs rhs^"}\n");
  print_string ("{"^munges pvs side^"}\n");
  print_string "{";
  (match comm with
     Some c -> print_string (munge pvs c)
   | None   -> ());
  print_string "}}\n\n"

(* render LTS from whole input stream *)
let lts_latex_render () =
  ignore (parse_rules_and_process latex_rule holtokstream)

(* render MNG from whole input stream *)

let pvs = ref []

let mng_latex_render () =
  Stream.iter (fun t -> match t with
                          DirBlk("VARS",ts) -> pvs := !pvs @ dir_var_vars ts
                        | _                 -> print_string (mtok !pvs t))
              textokstream

