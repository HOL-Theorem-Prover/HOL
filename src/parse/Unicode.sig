signature Unicode =
sig

  type term = Term.term
  (* functions for manipulating use of Unicode versions of constants *)
  val unicode_version : {u:string,tmnm:string} -> unit
  val temp_unicode_version : {u:string,tmnm:string} -> unit
  (*
  val disable_one_unicode : string -> unit
  val disable_one_unicode_t : term -> unit
  val enable_one_unicode : string -> unit
  val enable_one_unicode_t : term -> unit
  *)

  structure UChar : UnicodeChars

end

