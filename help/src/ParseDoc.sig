signature ParseDoc =
sig

  type substring = Substring.substring

  datatype markup = PARA
                  | TEXT of substring
                  | BRKT of substring
                  | XMPL of substring

  datatype section = TYPE of substring
                   | FIELD of string * markup list
                   | SEEALSO of substring list

  val parse_file : string -> section list
  exception ParseError of string

end;

(*

  [parse_file fname] takes fname, the name of a Doc-file, and parses it
  into a list of "sections", as per the datatypes above.

*)
