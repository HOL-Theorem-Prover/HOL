(* simpledump.ml -- test for Hollex *)
(* Keith Wansbrough 2001 *)

open Hollex

let rec render_token t =
  match t with
    Ident(s,_)   -> "I:"^s
  | Indent(n)    -> "\nN:"^(String.make n '>')
  | White(s)     -> "W:"^s
  | Comment(s)   -> "C:(*"^s^"*)-C"
  | DirBeg       -> "D+"
  | DirEnd       -> "-D"
  | DirBlk(n,ts) -> "D:"^n^": "^(String.concat " " (List.map render_token ts))^" :D"
  | Sep(s)       -> "S:"^s

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
