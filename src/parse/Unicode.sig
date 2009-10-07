signature Unicode =
sig

  type term = Term.term
  (* functions for manipulating use of Unicode versions of constants *)
  val unicode_version : {u:string,tmnm:string} -> unit
  val uoverload_on : string * term -> unit
  val uset_fixity : string -> Parse.fixity -> unit

  val temp_unicode_version : {u:string,tmnm:string} -> unit
  val temp_uoverload_on : string * term -> unit
  val temp_uset_fixity : string -> Parse.fixity -> unit

  structure UChar : UnicodeChars

end

