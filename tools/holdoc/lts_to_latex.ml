(* lts_to_latex.ml -- turn LTS (in HOL) into LaTeX code *)
(* Keith Wansbrough 2001 *)

open Hollex

exception Trailing (* there is trailing info in the file *)

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
    Ident(s)   -> "I:"^s
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
    [< 'Ident("!"); v = rule_vars; _ = sp; 'Sep(".") ?? "."; _ = sp; 
       'Indent(_);
       (n,cat,desc) = rule_name;
       l_lab_r = parse_chunk;
       'Indent(_);
       _ = sp'; 'Ident("<==") ?? n^": <=="; _ = sp;
       'Indent(_);
       side = parse_chunk;
       'Indent(_); _ = optind;
       comm = optcomm;
       _ = optind;
       _ = sp; 'Sep(")") ?? n^": rule end: `)'"; _ = sp >]
      -> let rec isLab ts =
            match ts with
              (Indent(_)   :: ts) -> isLab ts
            | (White(_)    :: ts) -> isLab ts
            | (Ident("--") :: _ ) -> true
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
  | [< 'Ident(s)  ; r = rule_vars >] -> s :: r
  | [<>]                             -> []

and rule_name = parser
    [< 'Indent(_); 'Ident(n) ?? "rule name"; _ = sp; 'Ident("/*") ?? "/*"; _ = sp; 'Ident(cat) ?? "category"; _ = wopt;
       desc = optcomm; _ = sp; 'Ident("*/") ?? "*/"; _ = sp >]
      -> (n,cat,desc)
  | [<>] -> raise (Stream.Error("rule name on new line"));


and parse_rules_and_process p = parser
    [< _ = sp'; rs = parse_rules_ap1 p >] -> rs
and parse_rules_ap1 p = parser
    [< 'Sep("("); _ = sp; r = (function ts -> p (parse_rule1 ts)); _ = sp';
       rs = parse_rules_ap2 p >] -> r :: rs
  | [<>]                         -> []
and parse_rules_ap2 p = parser
    [< 'Ident("/\\"); _ = sp';
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

let mtok t =
  match t with
    Ident(s)   -> texify s
  | Indent(n)  -> ""
  | White(s)   -> s
  | Comment(s) -> "\\text{\\small(*"^s^"*)}"
  | Sep(s)     -> texify s

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

let latex_rule (Rule(v,n,cat,desc,lhs,lab,rhs,side,comm)) =
  print_string ("\\rrule"^if side == [] then "n" else "c"
                         ^match comm with Some _ -> "c" | None -> "n");
  print_string ("{"^texify n^"}{"^texify cat^"}");
  print_string ("{"^(match desc with Some d -> texify d | None -> "")^"}\n");
  print_string ("{"^munges lhs^"}\n");
  print_string ("{"^munge lab^"}\n");
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


