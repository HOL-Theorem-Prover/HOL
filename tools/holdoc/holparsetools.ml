(* useful tools for using the parser and lexer *)

open Hollex

exception SyntaxError of string

(* display the current position in filename:line:col format *)
let pretty_pos lexbuf =
  let p = Lexing.lexeme_start_p lexbuf in
  p.Lexing.pos_fname ^ ":" 
  ^ string_of_int p.Lexing.pos_lnum ^ ":"
  ^ string_of_int (p.Lexing.pos_cnum - p.Lexing.pos_bol)

let parse mode nonterminal lexbuf =
  let lst = token_init mode lexbuf in
  try 
    nonterminal (fun _ -> token lst) lexbuf  (* ick - hack! *)
  with
    Parsing.Parse_error ->
      raise (SyntaxError ("unexpected token "^Lexing.lexeme lexbuf^" at "^pretty_pos lexbuf))

let parse_chan mode nonterminal chan =
  let lexbuf = Lexing.from_channel stdin in
  parse mode nonterminal lexbuf

(*
 * let parse_file mode nonterminal file =
 *   let lexbuf = Lexing.from_file file in
 *   parse mode nonterminal lexbuf
 *)  
