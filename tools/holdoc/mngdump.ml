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

exception BadArg of string located

let format_badarg : string located -> string
    = fun (s,l) ->
      format_location l ^ ": " ^ s

(* non-fatal error condition *)
let write_warning (s,l) =
  print_string ("% "^format_location l^"WARNING: "^s^".\n");
  prerr_endline (format_location l ^ "WARNING: " ^ s ^ ".")

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

(* last element of a list *)
let rec last = function
  | []  -> raise Not_found
  | [x] -> x
  | (x::xs) -> last xs

(* last location in list, or zero otherwise *)
let last_loc_or_zero ts =
  try
    let (_,l) = last ts in l
  with
    Not_found -> zero_loc

(* first location (if defined), else second *)
let orloc l1 l2 =
  if l1 = zero_loc then l2 else l1


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
          ((HolIdent(b,s),l)::ts) when List.mem s hol_binders
                  -> bdrs l vs ts
        | (_::ts) -> go vs ts
        | []      -> vs
      and bdrs l vs = function
          ((HolIdent(b,s)         ,_)::ts) -> bdrs l (s::vs) ts
        | ((HolDir (DirVARS bis,_),_)::ts) -> bdrs l (List.map snd bis @ vs) ts
        | ((HolDir (_          ,_),_)::ts) -> bdrs l vs ts  (* don't do the directive here! *)
        | ((HolSep s              ,_)::ts) -> go vs ts
        | (_ ::ts)  -> bdrs l vs ts
        | []        -> write_warning ("unexpected end of binder list",l); go vs []
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

let is_var_prefix s = List.mem s !(!curmodals.vAR_PREFIX_LIST)

let is_field s =  (* fields are treated specially *)
  try
    Hashtbl.find !curmodals.cLASS_IDS_LIST s = "FIELD"
  with
    Not_found -> false

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

let rec do_var0 depth v s =
  (* return fully texified variable or number, or raise Not_found if it's not a var *)
  if s = "" then
    raise Not_found
  (* commented out for now:
   * else if (List.mem s v || (depth < 1 && is_field s)) then
   *   (* field names often reused as var names *)
   *   "\\tsvar{"^texify_math s^"}"
   *)
  else if Str.string_match (Str.regexp "[0-9]+") s 0 then  (* digits *)
    s
  else
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
     || (!(!curmodals.sMART_PREFIX) &&
         (List.mem s0 v || is_field s0 ||
          List.mem (s0^s1^s2) v || is_field (s0^s1^s2))) then  (* treat as prefix *)
                                              (* if smart, always do foo1 -> foo_1;
                                                 otherwise, only if foo is specified as a prefix *)
    (let sbase = (try List.assoc s0 !(!curmodals.vAR_PREFIX_ALIST)
                  with Not_found -> "\\tsvar{"^texify_math s0^"}")
                 ^(if s2 <> "" then s2 else "")           (* primes *)
                 ^(if s1 <> "" then "_{"^s1^"}" else "")  (* digits *) in
     if s3 = "_" then
       "{"^sbase^"}_{"^do_var0 (depth+1) v s4^"}"  (* recurse on subscript; avoid TeX multiple-subscript error *)
     else
       sbase)  (* no recursion *)
  else
    raise Not_found (* not a variable *)
let do_var v s = do_var0 0 v s


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
  = fun ts0 cf ml ->
  let rec bal ps(*stack of closing delimiters*) ds(*tokens so far*) dss(*full args so far*) ts =
    let n = List.length ps
    in
    match ts with
      ((HolSep(s),_) as t::ts) when List.mem_assoc s balanced  (* open *)
        -> let ds' = if n=0 && cf then
                       ds
                     else
                       t::ds
           in
           bal (List.assoc s balanced::ps) ds' dss ts
    | ((HolSep(s),_) as t::ts) when n>0 && s = List.hd ps      (* close *)
        -> let ds' = if n=1 && cf then
                       ds
                     else
                       t::ds
           in
           if n=1 then
             (List.rev (List.rev ds' :: dss),ts)  (* we're done *)
           else
             bal (List.tl ps) ds' dss ts  (* pop *)
    | ((HolSep(s),l) as t::ts) when List.mem_assoc s flip_balanced && n>0 && s <> List.hd ps      (* close *)
        -> raise (BadArg ("6: expected closing delimiter "^List.hd ps^" but encountered "^s^" instead",l))
    | ((HolSep(","),_) as t::ts)
        -> if n=1 && cf then
             bal ps [] (List.rev ds::dss) ts
           else
             bal ps (t::ds) dss ts
    | ((HolIndent(_),l) as t::ts) ->
        if ml then
          bal ps (t::ds) dss ts
        else
          raise (BadArg ("7: line break not allowed in non-multiline curried op",l))
    | (t::ts)        -> bal ps (t::ds) dss ts
    | []             -> raise (BadArg ("1: unexpected end of input",last_loc_or_zero ts0))
  in
  bal [] [] [] ts0

let safedumphol_content =
  function
      (HolIndent n,_) -> "<indent>"
    | t -> dumphol_content t

let rec readarg cf ml ts0 = (* read a single arg: spaces then (id.id.id or matched-paren string) *)
  (* returns a list of lists of tokens because a single arg arity-wise may be
     multiple TeX arguments if cy_commas is in force *)
  let rec sp ts =  (* skip spaces (and newlines if allowed) *)
    match ts with
      ((HolWhite(_),_)::ts)          -> sp ts
    | ((HolIndent(_),_)::ts) when (ml || true) -> sp ts  (* hack: allow to always skip newlines - NB: this means that newlines /between/ arguments are _ignored_ *)
    | _                          -> ts
  in
  let rec dotted ds ts =  (* read a dotted arg *)
    match ts with
      (((HolSep("."),_) as t1)::((HolIdent(true,s),_) as t2)::ts)
                                    -> dotted (t2::t1::ds) ts
    | ((HolStr(_),l)::_)            -> raise (BadArg ("2: string unexpected",l))
    | ((HolIdent(_,_),l)::_)        -> raise (BadArg ("3: expected dot between idents",l))
    | _                             -> ([List.rev ds],ts)
  in
  match sp ts0 with
    (((HolIdent(true ,s),_) as t)::ts)  -> dotted [t] ts
  | (((HolIdent(false,s),_) as t)::ts)  -> ([[t]],ts)  (* no fields in a symbolic ident *)
  | (((HolSep(s)        ,_) as t)::ts) when List.mem_assoc s balanced
                          -> readbal (t::ts) cf ml
  | ((t,l)::ts)               -> raise (BadArg ("4: bad token "^safedumphol_content (t,l)^" follows curried op",l))
  | []                    -> raise (BadArg ("5: unexpected end of input",last_loc_or_zero ts0))


(* -------------------------------------------------------------------- *)
(*  Munging of each token class                                         *)
(* -------------------------------------------------------------------- *)

(* Some tokens are rendered differently in different contexts *)

type token_cxt = {
    adjid : bool;  (* previous non-space token was alphanumeric identifier *)
    bol   : bool;  (* first token on line *)
    indents : int list;  (* stack of current indentation levels *)
  }

let tcx0 : token_cxt = {
  adjid = false;
  bol = true;
  indents = [];
}


(* Do the munging *)

(* output a single alphanumeric identifier *)
let munge_ident : pvars -> string -> unit
    = fun pvs s ->
      let s_out =
        try List.assoc s !(!curmodals.hOL_ID_ALIST)
        with Not_found ->
          if (is_num s) then texify_math s else
          let normal c s = c^"{"^texify_math s^"}" in
          let under  c s = (let (sb,ss) = do_subscript s in c^"{"^sb^"}"^ss) in
          let copy   c s = c in
          let cliopt =
            try
              let cls = Hashtbl.find !curmodals.cLASS_IDS_LIST s in
              let cli = List.assoc cls !(!curmodals.cLASSES) in
              Some(cli)
            with
              Not_found -> None
          in
          let (c,sub) =
            match cliopt with
            | Some(cli) when cli.cl_highpri ->
                (cli.cl_cmd, if cli.cl_dosub then under else normal)
            | _ ->
                try
                  let c = do_var pvs s in
                  (c, copy)
                with
                  Not_found ->
                    match cliopt with
                    | Some(cli) ->
                        (cli.cl_cmd, if cli.cl_dosub then under else normal)
                    | None ->
                        log_unseen_string s;
                        ("\\tsunknown", normal)
          in
          sub c s
      in
      print_string s_out

      (* would be good to check is_* for overlaps *)

(* output a single symbolic identifier *)
(* boolean: is this ident at the beginning of a line? *)
let munge_symbol : pvars -> bool -> string -> unit
    = fun pvs bol s ->
      let s_out =
        try
          if bol then
            List.assoc s !(!curmodals.hOL_SYM_BOL_ALIST)
          else
            raise Not_found
        with Not_found -> 
          try List.assoc s !(!curmodals.hOL_SYM_ALIST)
          with Not_found ->
            texify_math s
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

(* output an indentation, correcting for the current indentation level *)
let munge_indent_ext : int list -> int -> unit
    = fun ms n ->
      match ms with
      | [] -> munge_indent n
      | (m::_) -> munge_indent (if m > n then 0 else n - m)


(* -------------------------------------------------------------------- *)
(*  Munging the whole document                                          *)
(* -------------------------------------------------------------------- *)

(* hook for preprocessing the content of TeX comments embedded in HOL *)
let rec render_HolTex_hook : (pvars -> texdoc -> unit) ref
    = ref begin
      fun pvs d ->
        wrap "\\tsholcomm{" "}" (rendertexdoc_pvs pvs) d
    end

(* output a single HOL token *)
(* boolean flag: was previous token an alphanumeric ident? *)
and munge_hol_content0 : pvars -> token_cxt -> hol_content -> token_cxt
    = fun pvs tcx (t,l) ->
      let render_it =
        match t with
          HolIdent(true ,s) -> (fun () ->
            if tcx.adjid then print_string "\\;";
            munge_ident pvs s)
        | HolIdent(false,s) -> (fun () -> munge_symbol pvs tcx.bol s)
        | HolStr s          -> (fun () -> wrap "\\text{``" "''}" munge_texify_text s)
        | HolWhite s        -> (fun () -> print_string s)
        | HolIndent n       -> (fun () -> munge_indent_ext tcx.indents n)
        | HolSep s          -> (fun () -> munge_texify_math s)
        | HolText d         -> (fun () ->
                               let s = dumptextdoc d in
                               wrap (if String.contains s '\n' then  (* "long" if split over a line *)
                                       "\\tslongcomm{"
                                     else
                                       "\\tscomm{") "}"
                                    munge_texify_text s)
        | HolTex d          -> (fun () -> !render_HolTex_hook pvs d)
        | HolDir (DirVARS _ ,_) -> (fun () -> ())    (* ignore *)
        | HolDir (dir       ,_) -> do_directive dir (* do it now, even if not echoing *);
                                   (fun () -> ())
      in
      if !eCHO then begin
        render_it ();
        let adjid' = match t with HolIdent(true,_) -> true | HolWhite _ -> tcx.adjid | _ -> false in
        let bol' = match t with HolIndent(_) -> true | HolWhite _ -> tcx.bol | _ -> false in
        let indents' = match t with
        | HolIdent(_,s) ->
            if List.mem s !(!curmodals.hOL_IOPEN_LIST) then
              (let m = snd (columns_of l) + 1 in
              m :: tcx.indents)
            else if List.mem s !(!curmodals.hOL_ICLOSE_LIST) then
              (match tcx.indents with
              | (_::tail) -> tail
              | [] -> write_warning ("Close delimiter without matching open",l); tcx.indents)
            else
              tcx.indents
        | _ -> tcx.indents in
        { tcx with adjid = adjid'; bol = bol'; indents = indents' }
      end else
        tcx  (* don't display anything if echoing turned off *)

and munge_hol_content : pvars -> hol_content -> unit
    = fun pvs tt ->
      let (_:token_cxt) = munge_hol_content0 pvs tcx0 tt in ()


(* output a curried op, returning the remainder of the stream *)
and munge_curried : pvars -> hol_content -> curried_info -> hol_content list -> hol_content list
  = fun pvs ((_,loc0) as x) info ts0 ->
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
    if info.cy_arity = 99 then  (* hack: turn off curried operator by setting arity to 99 *)
      (munge_hol_content pvs x; ts0)
    else
      go info.cy_arity [] ts0
  with
    BadArg(s,l) -> (* abort curry parse; do it uncurried *)
              let w = "curry parse failed: "^dumphol_content x^" ==> "^info.cy_cmd^" "^s
              in
              write_warning (w,orloc l loc0);
              munge_hol_content pvs x;
              ts0


(* output an entire HOL document *)
and munge_holdoc0 : pvars -> token_cxt -> holdoc -> token_cxt
    = fun pvs tcx ts ->
      match ts with
        []
          -> tcx

      | (((HolIdent(b,s),_) as t)::ts) when (match is_curried s with Some _ -> true | None -> false)
          -> (match is_curried s with
                Some info
                  -> let ts' = munge_curried pvs t info ts in
                     munge_holdoc0 pvs {tcx with adjid = false} ts'
              | _ -> raise (NeverHappen "munge_holdoc"))

      | (t::ts)
          -> let tcx' = munge_hol_content0 pvs tcx t in
             munge_holdoc0 pvs tcx' ts

and munge_holdoc : pvars -> holdoc -> unit
    = fun pvs ts -> let (_:token_cxt) = munge_holdoc0 pvs tcx0 ts in ()



(* The main set of rendering functions. *)

and rendertexdoc : texdoc -> unit
    = fun d -> rendertexdoc_pvs [] d

and rendertexdoc_pvs : pvars -> texdoc -> unit
    = fun pvs0 d -> List.iter (rendertexdoc_content_pvs pvs0) d

and rendertexdoc_content : texdoc_content -> unit
    = fun d -> rendertexdoc_content_pvs [] d

and rendertexdoc_content_pvs : pvars -> texdoc_content -> unit
    = fun pvs0 (t,_) -> match t with
    TexContent s -> print_string s
  | TexHol((ld,rd),d) ->
      local_set !curmodals.iNDENT false
        (wrap
           (match ld with
           | TexHolLR   -> !hOLDELIMOPEN
           | TexHolMath -> "")
           (match rd with
           | TexHolLR   -> !hOLDELIMCLOSE
           | TexHolMath -> "")
           (renderholdoc_pvs pvs0)) d
  | TexDir d -> texrenderdirective d

and texrenderdirective : directive -> unit
    = fun d -> texrenderdirective_content d

and texrenderdirective_content : directive_content -> unit
    = fun (d,_) -> do_directive d

and renderholdoc : holdoc -> unit
    = fun d ->
      renderholdoc_pvs [] d

and renderholdoc_pvs : pvars -> holdoc -> unit
    = fun pvs0 d ->
      let pvs = (if !(!curmodals.aUTO_BINDERS) then potential_vars d else []) @ pvs0
      in
      munge_holdoc pvs d


