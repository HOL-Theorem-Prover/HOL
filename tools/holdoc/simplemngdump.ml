open Holparse
open Holparsesupp
open Hollex


let lexbuf = Lexing.from_channel stdin
let lst = token_init ModeTex lexbuf
let _ = tex_main (fun _ -> token lst) lexbuf  (* ick - hack! *)


