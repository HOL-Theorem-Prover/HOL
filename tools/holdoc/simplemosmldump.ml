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
let _ = try 
  mosml_main (fun _ -> token lst) lexbuf  (* ick - hack! *)
with
  Parsing.Parse_error ->
    raise (Failure ("syntax error: token "^Lexing.lexeme lexbuf^" at "^pretty_pos lexbuf))




