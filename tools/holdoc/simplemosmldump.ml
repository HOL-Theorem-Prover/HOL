open Holdocmodel
open Holparse
open Holparsesupp
open Hollex


let pretty_pos lexbuf =
  let p = Lexing.lexeme_start_p lexbuf in
  p.Lexing.pos_fname ^ ":" 
  ^ string_of_int p.Lexing.pos_lnum ^ ":"
  ^ string_of_int (p.Lexing.pos_cnum - p.Lexing.pos_bol)

let lexbuf = Lexing.from_channel stdin
let lst = token_init ModeMosml lexbuf
let mosmldoc = try 
  mosml_main (fun _ -> token lst) lexbuf  (* ick - hack! *)
with
  Parsing.Parse_error ->
    raise (Failure ("syntax error: token "^Lexing.lexeme lexbuf^" at "^pretty_pos lexbuf))

let dolist f cs =
  String.concat "" (List.map f cs)

let dolines f (l0,ls) =
  let rec go ls = match ls with [] -> [] | ((n,l)::ls) -> (make_indent n ^ f l) :: go ls in
  f l0 ^ String.concat "" (go ls)


let rec dumptexdoc cs = dolist dumptexdoc_content cs
    
and dumptexdoc_content = function
    TexContent s -> s
  | TexHol(TexHolLR,d) -> "[[" ^ dumpholdoc d ^ "]]"
  | TexHol(TexHolMath,d) -> "<[" ^ dumpholdoc d ^ "]>"
  | TexDir d -> dumpdirective d

and dumptextdoc cs = dolist dumptextdoc_content cs

and dumptextdoc_content = function
    TextContent s -> s
  | TextText d -> "(*" ^ dumptextdoc d ^ "*)"
  | TextDir d -> dumpdirective d

and dumpmosmldoc cs = dolines dumpmosml_line cs

and dumpmosml_line cs = dolist dumpmosml_content cs

and dumpmosml_content = function
    MosmlContent s -> s
  | MosmlHol(io,md,d) ->
      let is = (match io with None -> "" | Some i -> i) in
      let bt = (match md with MosmlHolBT -> "`" | MosmlHolBTBT -> "``") in
      is ^ bt ^ dumpholdoc d ^ bt
  | MosmlText d -> "(*" ^ dumptextdoc d ^ "*)"
  | MosmlTex d -> "(*:" ^ dumptexdoc d ^ ":*)"
  | MosmlDir d -> dumpdirective d

and dumpholdoc cs = dolines dumphol_line cs

and dumphol_line cs = dolist dumphol_content cs

and dumphol_content = function
    HolIdent(b,s) -> s
  | HolStr s -> "\"" ^ s ^ "\""
  | HolWhite s -> s
  | HolSep s -> s
  | HolText d -> "(*" ^ dumptextdoc d ^ "*)"
  | HolTex d -> "(*:" ^ dumptexdoc d ^ ":*)"
  | HolDir d -> dumpdirective d

and dumpdirective d = dumpdirective_content d

and dumpdirective_content = function
    DirThunk f -> (f (); "")  (* do it now! (side-effecting) *)
  | DirVARS bis -> ""  (* ignore! *)


let s = dumpmosmldoc mosmldoc

let _ = print_string s
