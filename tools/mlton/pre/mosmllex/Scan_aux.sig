(* Scan_aux.sig *)

(* support specific to Scanner.lex *)

signature SCAN_AUX =
sig

  (* support for scanning actions and (nested) comments *)
  val brace_depth : int ref
  val comment_depth : int ref

  (* support for scanning strings *)
  val reset_string_buffer : unit -> unit
  val store_string_char : Char.char -> unit
  val get_stored_string : unit -> string
  val char_for_backslash : Char.char -> Char.char
  val char_for_decimal_code : 'a LexBuffer.lexbuf -> int -> Char.char

end (* signature SCAN_AUX *)
