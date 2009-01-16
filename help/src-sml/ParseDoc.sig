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

  val find_docfiles : string -> string Binaryset.set
  val core_dname : string -> string

end;

(*

  [parse_file fname] takes fname, the name of a Doc-file, and parses it
  into a list of "sections", as per the datatypes above.

  [find_docfiles dirname] scans the directory given by dirname, and
  returns a set of all the .doc files.  The doc files are stored in
  the set in an appropriate order, and stripped of their .doc suffix.

  [core_dname docfilename] takes docfilename, which must have been
  stripped of its .doc suffix and returns the "core" part of the name.
  For names of the form "struct.value", the core part is value.  For
  names of the form "value", the core part is simply value.  The latter
  sort of name occurs when .doc entries describe whole structures (e.g.,
  Absyn).


*)
