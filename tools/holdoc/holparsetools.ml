(* useful tools for using the parser and lexer *)

open Holparsesupp
open Hollex

exception SyntaxError of string

let parse mode nonterminal lexbuf =
  let lst = token_init mode lexbuf in
  try 
    nonterminal (fun _ ->
                   let t = token lst in
                   (* prerr_string ("«"^render_token t^"» "); *)
                   t) lexbuf  (* ick - hack! *)
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
