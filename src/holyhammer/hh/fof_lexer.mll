{
 open Lexing;;
 open Fof_parse;;
}

let white = [' ' '\t' '\r' '\n']
let letter = ['/' 'a'-'z' 'A'-'Z' '0'-'9' '_' '\'']
let any = [^ '\r' '\n']

rule hhlex = parse
| '%' any*           {hhlex lexbuf}
| '#' any*           {hhlex lexbuf}
| white+             {hhlex lexbuf}
| eof                {Eof}
| '('                {(*Printf.printf "(%!"; *)Openp}
| ')'                {(*Printf.printf ")%!"; *)Closep}
| '.'                {Dot}
| ','                {Comma}
| '!' white* '['     {(*Printf.printf "!%!"; *)All (lex_ids lexbuf)}
| '?' white* '['     {Exists (lex_ids lexbuf)}
| '='                {Eq}
| "!="               {Neq}
| '~'                {Tilde}
| "<=>"              {Eqvt}
| "<~>"              {Neqvt}
| "=>"               {(*Printf.printf ">%!"; *)Impl}
| '&'                {(*Printf.printf "&%!"; *)And}
| '|'                {Or}
| '$' letter+        {Word (Lexing.lexeme lexbuf)}
| letter+            {(*Printf.printf ".%!"; *)Word (Lexing.lexeme lexbuf)}
| '\'' [^ '\'']+ '\'' {(*Printf.printf ".%!"; *)Word (Lexing.lexeme lexbuf)}

and lex_ids = parse
| white+             {lex_ids lexbuf}
| letter+            {let i = Lexing.lexeme lexbuf in
                      i :: (lex_ids_more lexbuf)}

and lex_ids_more = parse
| white+             {lex_ids_more lexbuf}
| ','                {lex_ids lexbuf}
| ']' white* ':'     {[]}

{
Fusion.the_type_constants := ("$i", 0) :: !Fusion.the_type_constants;;
let read_fof fname =
  let inc =
    if fname = "-" then stdin else open_in fname in
  let lexb = Lexing.from_channel inc in
  let rec prf acc =
    try
      let v =
        try Fof_parse.hhtop hhlex lexb
        with Parsing.YYexit a -> Obj.magic a
      in
      prf (v :: acc)
    with End_of_file -> close_in inc; acc
  in
  prf []
;;

let rec print_fof_term tm =
  if Basics.is_forall tm then let (Fusion.Var(n,_),tm) = Basics.dest_forall tm in
    (print_string "!["; print_string n; print_string "]:"; print_fof_term tm) else
  if Basics.is_exists tm then let (Fusion.Var(n,_),tm) = Basics.dest_exists tm in
    (print_string "?["; print_string n; print_string "]:"; print_fof_term tm) else
  match tm with
    Fusion.Comb (_, _) ->
      begin match Basics.strip_comb tm with
        (Fusion.Const (op, _), argh :: argt) ->
          print_string (Hashtbl.find Fusion.hash_const_name op); print_string "("; print_fof_term argh; List.iter (fun i -> print_char ','; print_fof_term i) argt; print_char ')'
      | (Fusion.Var (s, _), argh :: argt) ->
          print_string s; print_string "("; print_fof_term argh; List.iter (fun i -> print_char ','; print_fof_term i) argt; print_char ')'
      | _ -> failwith "print_fof_term"
      end
  | Fusion.Const (s, _) -> print_string (Hashtbl.find Fusion.hash_const_name s)
  | Fusion.Var (s, _) -> print_string ("V" ^ s)
;;
}
