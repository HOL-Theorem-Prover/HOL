local
in
datatype token =
    ID of string
  | EQUALS
  | NULL
  | OPEN
  | QUAL_ID of string
  | STAR
  | EOF
end;

val MLtext :
  (Lexing.lexbuf -> token) -> Lexing.lexbuf -> string list;
