(* lts_to_latex.ml -- turn LTS (in HOL) into LaTeX code *)
(* Keith Wansbrough 2001-2004 *)

open Holdoc_init
open Holparse
open Holparsesupp
open Holparsetools
open Holdocmodel
open Simpledump
open Mngdump


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
      r_label       : holdoc;
      r_rhs         : holdoc;
      r_side        : holdoc;
      r_comment     : hol_content option;
    }

type definition_body =
    { d_name : string option;
      d_body : holdoc
    }

type type_body =
    { t_body : holdoc
    }

type item =
    Rule of rule_body
  | RuleSectionComment of hol_content
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
      let rec go n ds ds1 = function
          ((HolIndent(l) as d)::ts) ->
            if n = 0 then
              (List.rev (ds1@ds),ts)
            else
              go (n-1) ds (d::ds1) ts
        | (t::ts) ->
            go n0 (t::ds1@ds) ds1 ts
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
      let (label,ds) = parse_chunk 0 ("label of rule "^name) ds in
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
         r_side        = side       ;
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
            prerr_string ("Read rule "^r.r_name^"\n");
            let vs = Rule r :: vs in
            match ds with
              (HolIdent(false,"/\\")::ds) -> go vs ds
            | []                          -> List.rev vs
            | _ -> parsefail "/\\ or end of input" ("after parsing rule "^r.r_name) ds)
              (* section comment not allowed here; that belongs *above* the rules *)
        | ((HolText _ as d) :: ds)
        | ((HolTex  _ as d) :: ds) ->
            let ds = parse_sp' ds in
            prerr_string ("Read section comment\n");
            go (RuleSectionComment d::vs) ds
        | (HolIndent _ :: ds) ->
            go vs ds
        | (HolWhite _ :: ds) ->
            go vs ds
        | _ -> parsefail "rule or section comment" "while parsing LTS rules" ds
      in
      go [] ds

let parse_Define : hol_content list -> item
    = fun ds ->
      let name =  (* name is the first identifier in the body *)
        try
          match List.find isIdent ds with
            HolIdent(_,s) -> Some s
          | _ -> raise (NeverHappen "parse_Define")
        with
          Not_found -> None
      in
      Definition { d_name = name;
                   d_body = ds }

let parse_xDefine : string -> hol_content list -> item
    = fun name ds ->
      Definition { d_name = Some name;
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
                                        parseltsdoc0 ds (is'@is)
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
(*  Render whole file                                                   *)
(* -------------------------------------------------------------------- *)


let renderitem : item -> unit
    = function
        Rule r ->
          ()
      | RuleSectionComment d ->
          munge_hol_content [] d
      | Definition d ->
          renderholdoc d.d_body
      | Type t ->
          renderholdoc t.t_body
      | Directive f ->
          f ()

let renderitems : item list -> unit
    = List.iter renderitem


(* -------------------------------------------------------------------- *)
(*  Main program                                                        *)
(* -------------------------------------------------------------------- *)

let _ =
  !curmodals.rULES := true;
  let ltsdoc = parse_chan ModeMosml mosml_main stdin in
  print_string "%%%% AUTOGENERATED FILE (from LTS source) -- DO NOT EDIT! %%%%\n";
  let items = parseltsdoc ltsdoc in
  renderitems items


