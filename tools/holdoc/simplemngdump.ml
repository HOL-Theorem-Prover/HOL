open Holparse
open Holparsesupp
open Hollex


let lexbuf = Lexing.from_channel stdin
let lst = token_init ModeTex lexbuf
let _ = try 
  tex_main (fun _ -> token lst) lexbuf  (* ick - hack! *)
with
  Parsing.Parse_error ->
    raise (Failure ("syntax error: token "^Lexing.lexeme lexbuf^" at "^string_of_int (Lexing.lexeme_start lexbuf)))




