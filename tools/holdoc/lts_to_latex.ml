(* lts_to_latex.ml -- turn LTS (in HOL) into LaTeX code *)
(* Keith Wansbrough 2001-2004 *)

open Holdoc_init
open Holparse
open Holparsesupp
open Holparsetools
open Holdocmodel
open Simpledump
open Mngdump


(* see Net/TCP/Spec1/tags.txt for format and tag descriptions *)

(* -------------------------------------------------------------------- *)
(*  Diagnostics                                                         *)
(* -------------------------------------------------------------------- *)

exception Unimplemented of string


(* -------------------------------------------------------------------- *)
(*  Utilities                                                           *)
(* -------------------------------------------------------------------- *)
    
let isIdent : hol_content -> bool
    = function
        HolIdent _ -> true
      | _ -> false

let isIndent : hol_content -> bool
    = function
        HolIndent _ -> true
      | _ -> false

let optionCat : 'a option list -> 'a list
    = fun xs ->
      let rec go xs ys =
        match xs with
          [] -> List.rev ys
        | (Some x::xs) -> go xs (x::ys)
        | (None  ::xs) -> go xs ys
      in
      go xs []

let option : 'b -> ('a -> 'b) -> 'a option -> 'b
    = fun none some -> function
        None   -> none
      | Some x -> some x

let isNone : 'a option -> bool
    = function
        None -> true
      | Some _ -> false

let ($) : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c
    = fun f g x ->
      f (g x)

(* turn Not_found into None *)
let maybe : ('a -> 'b) -> 'a -> 'b option
  = fun f x
 -> try Some(f x) with Not_found -> None


(* -------------------------------------------------------------------- *)
(*  High-level document model                                           *)
(* -------------------------------------------------------------------- *)

type rule_body =
    { r_name        : string;
      r_var_list    : string list;
      r_proto       : string list;
      r_category    : string list;
      r_description : hol_content option;
      r_lhs         : holdoc;
      r_label       : string * holdoc * string;
      r_rhs         : holdoc;
      r_side        : holdoc option;
      r_comment     : hol_content option;
    }

type rulesectioncomment_body =
    { c_name : string;
      c_body : texdoc;
    }

type definition_body =
    { d_name : string;
      d_body : holdoc;
    }

type type_body =
    { t_body : holdoc;
    }

type item =
    Rule of rule_body
  | RuleSectionComment of rulesectioncomment_body
  | Definition of definition_body
  | Type of type_body
  | Directive of (unit -> unit)       (* a directive that is not inside an item *)


(* -------------------------------------------------------------------- *)
(*  Parser types and helpers                                            *)
(* -------------------------------------------------------------------- *)

exception ParseFail of string

let parsefail : string -> string -> hol_content list -> 'a
    = fun expected at -> function
        (d::_) -> raise (ParseFail ("Expected "^expected^" but found "^dumphol_content d^" "^at))
      | []     -> raise (ParseFail ("Expected "^expected^" but found end of input "^at))

type 'a holparser = hol_content list -> ('a * hol_content list)

type holparser_ = hol_content list -> hol_content list


(* -------------------------------------------------------------------- *)
(*  Fragment parsers                                                    *)
(* -------------------------------------------------------------------- *)

(* zero or more white space on one line *)
let rec parse_sp : holparser_
    = function
        (HolWhite  _ :: ds)
          -> parse_sp ds
      | ds -> ds

(* zero or more white space, may be multi-line *)
let rec parse_sp' : holparser_
    = function
        (HolWhite  _ :: ds)
      | (HolIndent _ :: ds)
          -> parse_sp' ds
      | ds -> ds

(* optional comment *)
let rec parse_optcomm : hol_content option holparser
    = function
        ((HolText _ as d) :: ds) -> (Some d,ds)
      | ((HolTex  _ as d) :: ds) -> (Some d,ds)
      | ds                       -> (None,  ds)

(* particular token *)
let parse_x : hol_content -> string -> holparser_
    = fun x s -> function
        (d::ds) when d = x -> ds
      | ds -> parsefail (dumphol_content x) s ds

(* rule variable list *)
let parse_rulevars : string -> string list holparser
    = fun rulename ->
      let rec go vs = function
        (HolIdent(b,s)        ::ts) -> go (s::vs) ts
      | (HolDir (DirVARS bis) ::ts) -> go (List.map snd bis @ vs) ts
      | (HolWhite _           ::ts)
      | (HolIndent _          ::ts) -> go vs ts
      | (HolSep "."           ::ts) -> (List.rev vs,ts)
      | ts -> parsefail "ident, space, or separator" ("while parsing rule "^rulename^" variable list") ts
    in
    go []

(* identifiers without intervening comments *)
let parse_idsnocomm : string list holparser
    = let rec go vs = function
        (HolIdent(true,s)::ts) -> go (s::vs) ts
      | (HolWhite _      ::ts) -> go vs ts
      | ts                     -> (List.rev vs, ts)
    in
    go []

(* all stuff until n blank lines *)
let parse_chunk : int -> string -> holdoc holparser
    = fun n0 s ->
      let rec go n ds ds_blanks = function
          ((HolIndent(l) as d)::ts) ->
            if n = 0 then
              (List.rev ds,ts)
            else
              go (n-1) ds (d::ds_blanks) ts
        | (t::ts) ->
            go n0 (t::ds_blanks@ds) [] ts
        | [] ->
            parsefail (string_of_int n0^" blank lines") s []
      in
      go n0 [] []

(* a newline *)
let parse_indent : string -> holparser_
    = fun s -> function
        (HolIndent _::ds) -> ds
      | ds -> parsefail "indent" s ds

(* an optional newline *)
let parse_optindent : holparser_
    = function
        (HolIndent _::ds) -> ds
      | ds -> ds

(* an identifier *)
let parse_ident : string -> string holparser
    = fun s -> function
        (HolIdent(_,s)::ds) -> (s,ds)
      | ds -> parsefail "ident" s ds

(* parse until "--" or "---" at start of line; blank line is an error;
   line on which token occurs is not included in parse. *)
let parse_lhs : string -> holdoc holparser
    = fun rulename ts ->
      (* number of newlines in a row;
         at start of line?
         tokens read so far on this line
         tokens read so far on previous lines
         start of line pointer
         input stream *)
      let rec go newlines start ds ds0 ts0 = function
          ((HolIndent _ :: _) as ts) when newlines >= 1 ->
            parsefail "label" ("while parsing lhs of rule "^rulename) ts
        | ((HolIndent _ as d)::ts) ->
            go (newlines+1) true [] (d::ds @ ds0) ts ts
        | ((HolWhite _ as d)::ts) ->
            go 0 start (d::ds) ds0 ts0 ts
        | (HolIdent(false,"--")::ts)
        | (HolIdent(false,"---")::ts) when start ->
            (List.rev ds0,ts0)
        | (d::ts) ->
            go 0 false (d::ds) ds0 ts0 ts
        | [] ->
            parsefail "lhs or label" ("while parsing lhs of rule "^rulename) []
      in
      go 0 true [] [] ts ts

(* parse label of rule *)
let parse_label : string -> (string * holdoc * string) holparser
    = fun rulename ts ->
      let arrowlefts = ["--";"---"] in
      let arrowrights = ["-->";"--->";"--=>"] in
      let rec go1 = function
          (HolWhite _::ts) -> go1 ts
        | (HolIdent(_,s)::ts) when List.mem s arrowlefts
              -> go2 s [] ts
        | ts -> parsefail "label arrow" ("when looking for label of rule "^rulename) ts
      and go2 s1 ds = function
          (HolIdent(_,s)::ts) when List.mem s arrowrights ->
              go3 s1 (List.rev ds) s ts
        | ((HolIndent _ :: _) as ts) ->
            parsefail "end of label arrow" ("when reading label of rule "^rulename) ts
        | (t::ts) -> go2 s1 (t::ds) ts
        | [] -> parsefail "end of label arrow" ("when reading label of rule "^rulename) []
      and go3 s1 lab s2 = function
          (HolWhite _::ts) -> go3 s1 lab s2 ts
        | (HolIndent _::ts) -> ((s1,lab,s2),ts)
        | ts -> parsefail "newline" ("after label of rule "^rulename) ts
      in
      go1 ts

(* parse an LTS rule *)
let parse_rule : rule_body holparser
    = fun ds ->
      let ds = parse_sp' ds in
      let ds = parse_x (HolSep("(")) "at start of rule" ds in
      let ds = parse_sp ds in
      let ds = parse_x (HolIdent(false,"!")) "at start of rule variable list" ds in
      let (var_list,ds) = parse_rulevars "<unknown>" ds in
      let ds = parse_sp' ds in
      let (name,ds) = parse_ident "while looking for rule name" ds in
      let ds = parse_sp ds in
      let ds = parse_x (HolIdent(false,"/*")) ("after rule "^name^" name") ds in
      let ds = parse_sp ds in
      let (proto,ds) = parse_idsnocomm ds in
      let ds = parse_x (HolSep(",")) ("after rule "^name^" protocol") ds in
      let ds = parse_sp ds in
      let (category,ds) = parse_idsnocomm ds in
      let ds = parse_sp ds in
      let (description,ds) = parse_optcomm ds in
      let ds = parse_sp ds in
      let ds = parse_x (HolIdent(false,"*/")) ("after rule "^name^" category and description") ds in
      let ds = parse_sp ds in
      let (lhs,ds) = parse_lhs name ds in
      let (label,ds) = parse_label name ds in
      let (rhs,ds) = parse_chunk 1 ("right-hand side of rule "^name) ds in
      let ds = parse_sp' ds in
      let ds = parse_x (HolIdent(false,"<==")) ("after conclusion of rule "^name) ds in
      let ds = parse_sp ds in
      let ds = parse_indent ("after <== in rule "^name) ds in
      let (side,ds) = parse_chunk 2 ("side condition of rule "^name) ds in
      let ds = parse_sp' ds in
      let (comment,ds) = parse_optcomm ds in
      let ds = parse_sp' ds in
      let ds = parse_x (HolSep ")") ("at end of rule "^name) ds in
      let ds = parse_sp' ds
      in
      ({ r_name        = name       ;
         r_var_list    = var_list   ;
         r_proto       = proto      ;
         r_category    = category   ;
         r_description = description;
         r_lhs         = lhs        ;
         r_label       = label      ;
         r_rhs         = rhs        ;
         r_side        = if List.for_all isIndent side then None else Some side;
         r_comment     = comment    ;
       }, ds)
         

(* -------------------------------------------------------------------- *)
(*  Parse item(s) from each chunk                                       *)
(* -------------------------------------------------------------------- *)

let parse_Net_Hol_reln : hol_content list -> item list
    = fun ds ->
      let ds = parse_sp' ds in
      let rec go vs ds =
        match ds with
          (HolSep("(") :: _) ->
            (let (r,ds) = parse_rule ds in
            let vs = Rule r :: vs in
            match ds with
              (HolIdent(false,"/\\")::ds) -> go vs ds
            | []                          -> List.rev vs
            | _ -> parsefail "/\\ or end of input" ("after parsing rule "^r.r_name) ds)
              (* section comment not allowed here; that belongs *above* the rules *)
        | (HolTex ts :: ds) ->
            let ds = parse_sp' ds in
            go (RuleSectionComment { c_name = "";  (* filled in later  *)
                                     c_body = ts }::vs) ds
        | (HolIndent _ :: ds) ->
            go vs ds
        | (HolWhite _ :: ds) ->
            go vs ds
        | _ -> parsefail "rule or section comment" "while parsing LTS rules" ds
      in
      let rec patch_rsc_name ys = function
          (RuleSectionComment c :: Rule r :: rs) ->
            patch_rsc_name (RuleSectionComment {c with c_name = r.r_name}::ys) (Rule r::rs)
        | (RuleSectionComment c :: r :: rs) ->
            raise (ParseFail ("Rule section comment without immediately-following rule"))
        | (r::rs) ->
            patch_rsc_name (r::ys) rs
        | [] -> List.rev ys
      in
      patch_rsc_name [] (go [] ds)

let parse_Define : hol_content list -> item
    = fun ds ->
      let name =  (* name is the first identifier in the body *)
        try
          match List.find isIdent ds with
            HolIdent(_,s) -> s
          | _ -> raise (NeverHappen "parse_Define")
        with
          Not_found -> raise (ParseFail ("Definition without obvious name"))
      in
      Definition { d_name = name;
                   d_body = ds }

let parse_xDefine : string -> hol_content list -> item
    = fun name ds ->
      Definition { d_name = name;
                   d_body = ds }

let parse_Hol_datatype : hol_content list -> item
    = fun ds ->
      Type { t_body = ds }  (* TODO: parse properly *)


let skiptext : textdoc -> unit
    = fun ds ->
      List.iter (function TextDir (DirThunk f) -> raise (Unimplemented ("Directive in MoSML text comment")) | _ -> ()) ds

let skiptex : texdoc -> unit
    = fun ds ->
      List.iter (function TexDir (DirThunk f) -> raise (Unimplemented ("Directive in MoSML TeX comment")) | _ -> ()) ds


(* -------------------------------------------------------------------- *)
(*  Parse whole file                                                    *)
(* -------------------------------------------------------------------- *)

(* parse all the items from a mosml_content stream: worker.
   Results prepended onto 'is' in reverse order. *)
let rec parseltsdoc0 : mosml_content list -> item list -> item list
    = fun ds is ->
      match ds with
        [] -> is
      | (d::ds) ->
          match d with
            MosmlContent s -> parseltsdoc0 ds is
          | MosmlStr s     -> parseltsdoc0 ds is
          | MosmlIndent n  -> parseltsdoc0 ds is
          | MosmlHol(Some (tag,strs),MosmlHolBT,d') ->
              (match (tag,strs) with
                ("Net_Hol_reln",[] ) -> let is' = parse_Net_Hol_reln d' in
                                        parseltsdoc0 ds (List.rev is' @ is)
              | ("Define"      ,[] ) -> let i = parse_Define d' in
                                        parseltsdoc0 ds (i::is)
              | ("xDefine"     ,[s]) -> let i = parse_xDefine s d' in
                                        parseltsdoc0 ds (i::is)
              | ("Hol_datatype",[] ) -> let i = parse_Hol_datatype d' in
                                        parseltsdoc0 ds (i::is)
              | _ ->
                  raise (Unimplemented ("Tag "^tag^" unimplemented or extra string, sorry!")))
          | MosmlHol(_,_,_) ->
              raise (Unimplemented ("Tagless or double-backticked item unimplemented, sorry!"))
          | MosmlText d -> (skiptext d; parseltsdoc0 ds is)
          | MosmlTex d -> (skiptex d; parseltsdoc0 ds is)
          | MosmlDir (DirThunk f) -> parseltsdoc0 ds (Directive f::is)
          | MosmlDir (DirVARS _) -> parseltsdoc0 ds is
            

(* parse all the items from a mosmldoc *)
let parseltsdoc : mosmldoc -> item list
    = fun d ->
      List.rev (parseltsdoc0 d [])


(* -------------------------------------------------------------------- *)
(*  LTS documentation mid-level model                                   *)
(* -------------------------------------------------------------------- *)

type ldoctag =
    (* cluster comment tags *)
    LdocPreamble
  | LdocSection of string
  | LdocErrors
  | LdocError of string
  | LdocSeealso of string
  | LdocCommoncases
  | LdocApi
  | LdocModeldetails
    (* rule comment tags *)
  | LdocDescription
(*| LdocModeldetails - as above *)
  | LdocVariation of string
  | LdocInternal


(* list of tag, body pairs *)
type ldoc_mid = (ldoctag * texdoc) list


(* -------------------------------------------------------------------- *)
(*  Parse LTS documentation - mid-level                                 *)
(* -------------------------------------------------------------------- *)

let white_re = Str.regexp "[ \t]+"
let dir_re = Str.regexp "@\\([A-Za-z0-9_]*\\)"

let rec parse_line0_rev : texdoc -> texdoc -> texdoc * texdoc
    = fun seen ds ->
      match ds with
        []                         -> (seen,[])
      | ((TexHol _    ) as d :: ds)
      | ((TexDir _    ) as d :: ds) -> parse_line0_rev (d::seen) ds
      | ((TexContent s) as d :: ds) ->
          match maybe (String.index s) '\n' with
            None                    -> parse_line0_rev (d::seen) ds
          | Some i ->
              (TexContent (String.sub s 0 i) :: seen,
               TexContent (String.sub s (i+1) (String.length s - (i+1))) :: ds)

(* returns the REVERSED parsed line and the remainder *)
let parse_line_rev : texdoc -> texdoc * texdoc
    = fun ds ->
      parse_line0_rev [] ds


let tidy : string -> string
    = fun s ->
      if Str.string_match white_re s 0 then
        Str.string_after s (Str.match_end ())
      else
        s

let assertempty : string -> string -> unit
    = fun tag s ->
      if tidy s <> "" then raise (ParseFail ("LDoc tag "^tag^": unexpected argument(s) "^s)) else ()


let rec hasTag1 : string -> string -> texdoc -> ldoctag
    = fun tag s ds ->
      match ds with
        (TexContent s' :: ds) -> hasTag1 tag (s^s') ds
      | (d :: ds) -> raise (ParseFail ("LDoc tag "^tag^" given non-TeX argument "^dumptexdoc_content d))
      | [] ->
          match tag with
            "section"      -> LdocSection (tidy s)
          | "errors"       -> assertempty tag s; LdocErrors
          | "error"        -> LdocError (tidy s)
          | "seealso"      -> LdocSeealso (tidy s)
          | "commoncases"  -> assertempty tag s; LdocCommoncases
          | "api"          -> assertempty tag s; LdocApi
          | "modeldetails" -> assertempty tag s; LdocModeldetails
          | "description"  -> assertempty tag s; LdocDescription
          | "variation"    -> LdocVariation (tidy s)
          | "internal"     -> assertempty tag s; LdocInternal 
          | _ -> raise (ParseFail ("unrecognised LDoc tag "^tag))


(* assumes directive won't be broken across TexContent items *)
let rec hasTag : texdoc -> ldoctag option
    = fun ds ->
      match ds with
        [] -> None
      | (TexHol _     :: ds)
      | (TexDir _     :: ds) -> None
      | (TexContent s :: ds) ->
          if Str.string_match white_re s 0 then
            let s' = Str.string_after s (Str.match_end ()) in
            if s' = "" then hasTag ds else hasTag (TexContent s' :: ds)
          else if Str.string_match dir_re s 0 then
            let s' = Str.matched_group 1 s in
            let s'' = Str.string_after s (Str.match_end ()) in
            Some (hasTag1 s' s'' ds)
          else
            None
            

let rec ltsdoc0 : ldoctag -> texdoc -> texdoc -> ldoc_mid -> ldoc_mid
    = fun tag seen ds ls ->
      match ds with
        [] -> List.rev ((tag,List.rev seen)::ls)
      | _  ->
          let (line_rev,ds) = parse_line_rev ds in
          match hasTag (List.rev line_rev) with
            None      -> ltsdoc0 tag (line_rev @ seen) ds ls
          | Some tag' -> ltsdoc0 tag' [] ds ((tag,List.rev seen)::ls)
                
let ltsdoc : texdoc -> ldoc_mid
    = fun ds ->
      ltsdoc0 LdocPreamble [] ds []


(* -------------------------------------------------------------------- *)
(*  LTS documentation high-level model                                  *)
(* -------------------------------------------------------------------- *)

type ldoc_cluster =
    { ldc_sectionname : string;
      ldc_preamble : texdoc;
      ldc_errors_preamble : texdoc;
      ldc_errors : (string * texdoc) list;
      ldc_seealso : (string * texdoc) list;
      ldc_commoncases : texdoc;
      ldc_api : texdoc;
      ldc_modeldetails : texdoc;
    }

type ldoc_rule =
    { ldr_description : texdoc;
      ldr_modeldetails : texdoc;
      ldr_variation : (string * texdoc) list;
      ldr_internal : texdoc;
    }


(* -------------------------------------------------------------------- *)
(*  Render whole file                                                   *)
(* -------------------------------------------------------------------- *)

let strip : holdoc -> holdoc
    = fun d ->
      if !(!curmodals.cOMMENTS) then
        d
      else
        let is_interesting = function
            HolIndent(_) -> false
          | HolWhite(_)  -> false
          | HolTex(_)    -> false
          | HolText(_)   -> false
          | _            -> true
        in
        List.filter is_interesting d

(* render a transition label *)
let munge_label : pvars -> string * holdoc * string -> unit
    = fun pvs (s1,d,s2) ->
      wrap "\\inp{" "}" (munge_holdoc pvs) d

(* render an item to a TeX definition, 
   returning the TeX command name for that definition *)
let renderitem : item -> string option
    = function
        Rule r ->
          let cmd = texify_command "" r.r_name in
          let pvs =
            r.r_var_list
            @ potential_vars r.r_lhs
            @ potential_vars (match r.r_label with (_,x,_) -> x)
            @ potential_vars r.r_rhs
            @ option [] potential_vars r.r_side in
          let rrule = "\\rrule"
              ^ (if isNone r.r_side then "n" else "c")
              ^ (if isNone r.r_comment then "n" else "c") in
          wrap ("\\newcommand{"^cmd^"}{"
                ^rrule^"{"
                ^texify_math r.r_name^"}{"
                ^String.concat " " (List.map texify_math r.r_proto)^": "
                ^String.concat " " (List.map texify_math r.r_category)^"}"
               ) "}\n\n"
            (fun () ->
              wrap "{" "}\n" (option () (munge_hol_content pvs)) r.r_description;
              wrap "{" "}\n" (munge_holdoc pvs) (strip r.r_lhs);
              wrap "{" "}\n" (munge_label pvs) r.r_label;
              wrap "{" "}\n" (munge_holdoc pvs) (strip r.r_rhs);
              wrap "{" "}\n" (option () (munge_holdoc pvs $ strip)) r.r_side;
              wrap "{" "}\n" (option () (munge_hol_content pvs)) r.r_comment;
            ) ();
          Some cmd
      | RuleSectionComment c ->
          let cmd = texify_command "seccomm" c.c_name in
          wrap ("\\newcommand{"^cmd^"}{\\seccomm{") "}}\n\n"
            (munge_hol_content []) (HolTex c.c_body);
          Some cmd
      | Definition d ->
          let cmd = texify_command "defn" d.d_name in
          wrap ("\\newcommand{"^cmd^"}{\\ddefn{"^texify_math d.d_name^"}{") "}}\n\n"
            renderholdoc d.d_body;
          Some cmd
      | Type t ->
          raise (Unimplemented "renderitem: Type")
      | Directive f ->
          f ();
          None

let renderitems : item list -> string list
    = optionCat $ List.map renderitem


(* -------------------------------------------------------------------- *)
(*  Main program                                                        *)
(* -------------------------------------------------------------------- *)

let _ =
  !curmodals.rULES := true;
  let ltsdoc = parse_chan ModeMosml mosml_main stdin in
  print_string "%%%% AUTOGENERATED FILE (from LTS source) -- DO NOT EDIT! %%%%\n";
  let items = parseltsdoc ltsdoc in
  let cmds = renderitems items in
  wrap "\\newcommand{\\dumpallrules}{\n" "}\n\n"
    (List.iter (fun rn -> print_string ("\\showrule{"^rn^"}\n"))) cmds;
  (match !rCSID with
    Some s -> print_string ("\\newcommand{\\rulesrcsid}{"^texify_text s^"}\n\n")
  | None   -> ());
  print_string "%%%% END %%%%\n"



