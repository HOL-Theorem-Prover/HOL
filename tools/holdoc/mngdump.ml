(* mngdump  -- render into LaTeX code *)
(* Keith Wansbrough 2001-2004 *)

open Holdoc_init
open Holparse
open Holparsesupp
open Holparsetools
open Holdocmodel
open Simpledump


(* -------------------------------------------------------------------- *)
(*  Diagnostics                                                         *)
(* -------------------------------------------------------------------- *)

exception BadArg of string

(* non-fatal error condition *)
let write_warning s =
  print_string ("% WARNING: "^s^".\n");
  prerr_endline ("WARNING: " ^ s ^ ".")

(* log an unrecognised string *)
let unseen_strings = Hashtbl.create 100
let log_unseen_string s =
  try
    let n = Hashtbl.find unseen_strings s in
    Hashtbl.remove unseen_strings s;
    Hashtbl.add unseen_strings s (n+1)
  with
    Not_found ->
      Hashtbl.add unseen_strings s 1
let dump_unseen_strings () =
  let keys = ref [] in
  Hashtbl.iter (fun s _ -> keys := s :: !keys) unseen_strings;
  let keys = List.sort String.compare !keys in
  prerr_endline (string_of_int (List.length keys) ^ " unseen strings:");
  List.iter (fun s -> Printf.fprintf stderr "%20s %4d\n" s (Hashtbl.find unseen_strings s)) keys;
  prerr_endline "(end)"


(* -------------------------------------------------------------------- *)
(*  Helpers                                                             *)
(* -------------------------------------------------------------------- *)

(* print delimiters around the output of a function *)
let wrap s0 s1 f v =
  print_string s0;
  f v;
  print_string s1

(* n copies of an item *)
let replicate n x =
  let rec go n xs =
    if n <= 0 then xs else go (n-1) (x::xs)
  in
  go n []

(* set a global and restore it afterwards *)
let local_set r v f x =
  let old_v = !r in
  r := v;
  let y = f x in
  r := old_v;
  y


(* -------------------------------------------------------------------- *)
(*  HOL helpers                                                         *)
(* -------------------------------------------------------------------- *)

(* compute the set of potential vars from a HOL fragment,
   ie, all idents that are bound somewhere *)

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

type pvars = string list

let potential_vars : holdoc -> pvars
    = fun d ->
      let rec go vs = function
          (HolIdent(b,s)::ts) when List.mem s hol_binders
                  -> bdrs vs ts
        | (_::ts) -> go vs ts
        | []      -> vs
      and bdrs vs = function
          (HolIdent(b,s)::ts) -> bdrs (s::vs) ts
        | (HolDir (DirVARS bis) ::ts) -> bdrs (List.map snd bis @ vs) ts
        | (HolDir (DirThunk f)  ::ts) -> bdrs vs ts  (* don't do the directive here! *)
        | (HolSep s     ::ts) -> go vs ts
        | (_ ::ts)            -> bdrs vs ts
        | []                  -> write_warning "unexpected end of binder list"; go vs []
      in
      go [] d


(* -------------------------------------------------------------------- *)
(*  TeXification                                                        *)
(* -------------------------------------------------------------------- *)

(* Printing various tokens nicely in TeX *)

(* converting a string to a TeX-printable form (assuming math mode in some cases) *)

let texify_math_list =
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
  ;('<', "\\textless{}")  (* the {} is to work around a bug in LaTeX / fontenc: \textless\textless == \textguillemotleft  (!!!) *)
  ;('>', "\\textgreater{}")  (* the {} is to work around a bug in LaTeX / fontenc *)
  ]

let texify_command prefix s =
  let f s = String.make 1 (char_of_int
                             (int_of_string
                                (Str.matched_string s)
                                + int_of_char 'A' - 1))
  in
   "\\" ^ prefix ^
   Str.global_replace    (Str.regexp "[^A-Za-z0-9]") "X"
  (Str.global_substitute (Str.regexp "[0-9]+"      )  f
                         s)


let dotexify tlist =
  let re = Str.regexp (String.concat "\\|" (List.map (function (c,_) -> Str.quote (String.make 1 c)) tlist))
  in
  let go s =
    match s with
      Str.Text(s)  -> s
    | Str.Delim(s) -> List.assoc (String.get s 0) tlist
  in
  function s ->
    String.concat "" (List.map go (Str.full_split re s))

let texify_math = dotexify texify_math_list

let texify_text = dotexify texify_text_list


(* -------------------------------------------------------------------- *)
(*  Syntactic categories                                                *)
(* -------------------------------------------------------------------- *)

(* recognisers for various syntactic categories *)

let is_rule s =
  !(!curmodals.rULES) &&
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
             (Str.regexp "\\([0-9]*\\)\\([']*\\)$")
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

let is_holop s = List.mem s !(!curmodals.hOL_OP_LIST)



(* -------------------------------------------------------------------- *)
(*  Rendering of variables                                              *)
(* -------------------------------------------------------------------- *)

let do_subscript s =
  (* return texified body (will be wrapped in typestyle)
     and texified suffix (will be appended) *)
  let _ = (Str.search_forward
             (Str.regexp "\\([0-9]*\\)\\([']*\\)$")
             s
             0 ) in
  if "" <> (Str.matched_group 1 s) then
    (texify_math (Str.string_before s (Str.match_beginning ())),
     "_{"^Str.matched_group 1 s^"}"^Str.matched_group 2 s)
  else
    (texify_math s,"")

let rec do_var v s =
  (* return fully texified variable or number, or raise Not_found if it's not a var *)
  if s = "" then raise Not_found else
  let _ = (Str.search_forward
             (Str.regexp "\\([0-9]*\\)\\([']*\\)\\($\\|_\\)")  (* always matches *)
             s
             1 ) in  (* must have at least one non-suffix character *)
  let (s0,s1,s2,s3,s4) = (Str.string_before s (Str.match_beginning ()),
                          Str.matched_group 1 s,
                          Str.matched_group 2 s,
                          Str.matched_group 3 s,
                          Str.string_after s (Str.match_end ())) in
  if    List.mem s0 !(!curmodals.vAR_PREFIX_LIST)
     || List.mem_assoc s0 !(!curmodals.vAR_PREFIX_ALIST)
     || ((List.mem s0 v || is_field s0) && !(!curmodals.sMART_PREFIX)) then (* treat as prefix *)
                                              (* if smart, always do foo1 -> foo_1;
                                                 otherwise, only if foo is specified as a prefix *)
    (let sbase = (try List.assoc s0 !(!curmodals.vAR_PREFIX_ALIST)
                  with Not_found -> "\\tsvar{"^texify_math s0^"}")
                 ^(if s2 <> "" then s2 else "")           (* primes *)
                 ^(if s1 <> "" then "_{"^s1^"}" else "")  (* digits *) in
     if s3 = "_" then
       "{"^sbase^"}_{"^do_var v s4^"}"  (* recurse on subscript; avoid TeX multiple-subscript error *)
     else
       sbase)  (* no recursion *)
  else if List.mem s v || is_field s then  (* field names often reused as var names *)
    "\\tsvar{"^texify_math s^"}"
  else if Str.string_match (Str.regexp "[0-9]+") s 0 then  (* digits *)
    s
  else
    raise Not_found (* not a variable *)


(* -------------------------------------------------------------------- *)
(*  Parsing and rendering of curried identifier applications            *)
(* -------------------------------------------------------------------- *)

let balanced = [ ("(",")"); ("[","]"); ("{","}")]

let flip_balanced = List.map (fun (x,y) -> (y,x)) balanced

let readbal : hol_content list        (* input stream *)
           -> bool                    (* convert level 1 commas to "}{" and remove level 1 parens *)
           -> bool                    (* allow multi-line *)
           -> (hol_content list list *   (* the arg (may be multiple args if cf) *)
               hol_content list)         (* the remainder *)
  = fun ts cf ml ->
  let rec bal ps(*stack of closing delimiters*) ds(*tokens so far*) dss(*full args so far*) ts =
    let n = List.length ps
    in
    match ts with
      (HolSep(s) as t::ts) when List.mem_assoc s balanced  (* open *)
        -> let ds' = if n=0 && cf then
                       ds
                     else
                       t::ds
           in
           bal (List.assoc s balanced::ps) ds' dss ts
    | (HolSep(s) as t::ts) when n>0 && s = List.hd ps      (* close *)
        -> let ds' = if n=1 && cf then
                       ds
                     else
                       t::ds
           in
           if n=1 then
             (List.rev (List.rev ds' :: dss),ts)  (* we're done *)
           else
             bal (List.tl ps) ds' dss ts  (* pop *)
    | (HolSep(s) as t::ts) when List.mem_assoc s flip_balanced && n>0 && s <> List.hd ps      (* close *)
        -> raise (BadArg ("6: expected closing delimiter "^List.hd ps^" but encountered "^s^" instead"))
    | (HolSep(",") as t::ts)
        -> if n=1 && cf then
             bal ps [] (List.rev ds::dss) ts
           else
             bal ps (t::ds) dss ts
    | (HolIndent(_) as t::ts) ->
        if ml then
          bal ps (if n=1 then ds else t::ds) dss ts  (* strip first-level indentation of multiline *)
        else
          raise (BadArg ("7: line break not allowed in non-multiline curried op"))
    | (t::ts)        -> bal ps (t::ds) dss ts
    | []             -> raise (BadArg ("1: unexpected end of input"))
  in
  bal [] [] [] ts

let safedumphol_content =
  function
      HolIndent n -> "<indent>"
    | t -> dumphol_content t

let rec readarg cf ml ts = (* read a single arg: spaces then (id.id.id or matched-paren string) *)
  (* returns a list of lists of tokens because a single arg arity-wise may be
     multiple TeX arguments if cy_commas is in force *)
  let rec sp ts =  (* skip spaces (and newlines if allowed) *)
    match ts with
      (HolWhite(_)::ts)          -> sp ts
    | (HolIndent(_)::ts) when ml -> sp ts
    | _                          -> ts
  in
  let rec dotted ds ts =  (* read a dotted arg *)
    match ts with
      ((HolSep(".") as t1)::(HolIdent(true,s) as t2)::ts)
                                    -> dotted (t2::t1::ds) ts
    | (HolStr(_)::_)                -> raise (BadArg "2: string unexpected")
    | (HolIdent(_,_)::_)            -> raise (BadArg "3: expected dot between idents")
    | _                             -> ([List.rev ds],ts)
  in
  match sp ts with
    ((HolIdent(true ,s) as t)::ts)  -> dotted [t] ts
  | ((HolIdent(false,s) as t)::ts)  -> ([[t]],ts)  (* no fields in a symbolic ident *)
  | ((HolSep(s) as t)::ts) when List.mem_assoc s balanced
                          -> readbal (t::ts) cf ml
  | (t::ts)               -> raise (BadArg ("4: bad token "^safedumphol_content t^" follows curried op"))
  | []                    -> raise (BadArg "5: unexpected end of input")


(* -------------------------------------------------------------------- *)
(*  Munging of each token class                                         *)
(* -------------------------------------------------------------------- *)


(* Do the munging *)

(* output a single alphanumeric identifier *)
let munge_ident : pvars -> string -> unit
    = fun pvs s ->
      let s_out =
        try List.assoc s !(!curmodals.hOL_ID_ALIST)
        with Not_found ->
          if (is_num s) then texify_math s else
          let normal c s = "\\"^c^"{"^texify_math s^"}" in
          let under  c s = (let (sb,ss) = do_subscript s in "\\"^c^"{"^sb^"}"^ss) in
          let copy   c s = c in
          let (c,sub)  = if (is_rule s)        then ("tsrule"    ,normal) else
                         if (is_con s)         then ("tscon"     ,normal) else
                         if (is_aux s)         then ("tsaux"     ,normal) else
                         if (is_aux_infix s)   then ("tsauxinfix",normal) else
                         if (is_lib s)         then ("tslib"     ,under ) else
                         try let c = do_var pvs s
                             in (c, copy)
                         with Not_found ->
                         if (is_holop s)       then ("tsholop"   ,normal) else
                         if (is_type s)        then ("tstype"    ,normal) else
                         (log_unseen_string s;      ("tsunknown" ,normal)) in
          sub c s
      in
      print_string s_out

      (* would be good to check is_* for overlaps *)

(* output a single symbolic identifier *)
let munge_symbol : pvars -> string -> unit
    = fun pvs s ->
      let s_out =
        try List.assoc s !(!curmodals.hOL_SYM_ALIST)
        with Not_found -> texify_math s
      in
      print_string s_out

(* output some text correctly for TeX LR mode *)
let munge_texify_text : string -> unit
    = fun s -> print_string (texify_text s)

(* output a symbol correctly for TeX math mode *)
let munge_texify_math : string -> unit
    = fun s -> print_string (texify_math s)

(* output an indentation *)
let munge_indent : int -> unit
    = fun n ->
      if !(!curmodals.iNDENT) then  (* only render if desired *)
        let m = (n-5) /2 in
        print_string ("{}\\\\{}\n" ^ String.concat "" (replicate m "\\quad") ^ " ")
      else
        print_string "\n"


(* -------------------------------------------------------------------- *)
(*  Munging the whole document                                          *)
(* -------------------------------------------------------------------- *)


(* output a single HOL token *)
let rec munge_hol_content : pvars -> hol_content -> unit
    = fun pvs t ->
      let render_it =
        match t with
          HolIdent(true ,s) -> (fun () -> munge_ident pvs s)
        | HolIdent(false,s) -> (fun () -> munge_symbol pvs s)
        | HolStr s          -> (fun () -> wrap "\\text{``" "''}" munge_texify_text s)
        | HolWhite s        -> (fun () -> print_string s)
        | HolIndent n       -> (fun () -> munge_indent n)
        | HolSep s          -> (fun () -> munge_texify_math s)
        | HolText d         -> (fun () ->
                               let s = dumptextdoc d in
                               wrap (if String.contains s '\n' then  (* "long" if split ove r a line *)
                                       "\\tslongcomm{"
                                     else
                                       "\\tscomm{") "}"
                                    munge_texify_text s)
        | HolTex d          -> (fun () -> wrap "\\tsholcomm{" "}" rendertexdoc d)
        | HolDir (DirThunk f) -> f () (* do it now, even if not echoing *);
                                 (fun () -> ())
        | HolDir (DirVARS _)  -> (fun () -> ())    (* ignore *)
      in
      if !eCHO then
        render_it ()
      else
        ()  (* don't display anything if echoing turned off *)


(* output a curried op, returning the remainder of the stream *)
and munge_curried : pvars -> hol_content -> curried_info -> hol_content list -> hol_content list
  = fun pvs x info ts ->
  let rec go n args ts =
    if n <= 0 then
      (print_string info.cy_cmd;
       List.iter (wrap "{" "}" (munge_holdoc pvs)) (List.rev args);
       ts)
    else
      match readarg info.cy_commas info.cy_multiline ts with
        (dss,ts) -> go (n-1) (List.rev_append dss args) ts
  in
  try
    go info.cy_arity [] ts
  with
    BadArg(s) -> (* abort curry parse; do it uncurried *)
              let w = "curry parse failed: "^dumphol_content x^" ==> "^info.cy_cmd^" "^s
              in
              write_warning w;
              munge_hol_content pvs x;
              ts


(* output an entire HOL document *)
and munge_holdoc : pvars -> holdoc -> unit
    = fun pvs ts ->
      match ts with
        []
          -> ()

      | ((HolIdent(b,s) as t)::ts) when (match is_curried s with Some _ -> true | None -> false)
          -> (match is_curried s with
                Some info
                  -> let ts' = munge_curried pvs t info ts
                     in
                     munge_holdoc pvs ts'
              | _ -> raise (NeverHappen "munge_holdoc"))

      | (t::ts)
          -> (munge_hol_content pvs t;
              munge_holdoc pvs ts)



(* The main set of rendering functions. *)

and rendertexdoc : texdoc -> unit
    = fun d -> List.iter rendertexdoc_content d

and rendertexdoc_content : texdoc_content -> unit
    = function
    TexContent s -> print_string s
  | TexHol(TexHolLR,d) ->
      local_set !curmodals.iNDENT false
        (wrap (!hOLDELIMOPEN) (!hOLDELIMCLOSE) renderholdoc) d
  | TexHol(TexHolMath,d) ->
      local_set !curmodals.iNDENT false
        (wrap "" "" renderholdoc) d
  | TexDir d -> texrenderdirective d

and texrenderdirective : directive -> unit
    = fun d -> texrenderdirective_content d

and texrenderdirective_content : directive_content -> unit
    = function
        DirThunk f -> f ()
      | DirVARS bis -> ()   (* ignore VARS in TeX mode *)

and renderholdoc : holdoc -> unit
    = fun d ->
      let pvs = potential_vars d
      in
      munge_holdoc pvs d


