(* simpledump.ml -- test for Hollex *)
(* Keith Wansbrough 2001 *)

open Hollex

let render_token t =
  match t with
    Ident(s)   -> "I:"^s
  | Indent(n)  -> "\nN:"^(String.make n '>')
  | White(s)   -> "W:"^s
  | Comment(s) -> "C:(*"^s^"*)-C"
  | Sep(s)     -> "S:"^s

let _ =
  let lexbuf = Lexing.from_channel stdin in
  relheader lexbuf ;
  try
    while true do
      let result = reltoken lexbuf in
      print_string ((render_token result)^" ");
    done
  with
    Finished -> ()
