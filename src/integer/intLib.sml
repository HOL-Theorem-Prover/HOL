structure intLib :> intLib =
struct

  open HolKernel Abbrev intSyntax intSimps Cooper
  val (Type,Term) = Parse.parse_from_grammars integerTheory.integer_grammars

  val operators = [("+", ``$+ : int -> int -> int``),
                   ("-", ``$- : int -> int -> int``),
                   ("*", ``$* : int -> int -> int``),
                   ("/", ``$/ : int -> int -> int``),
                   ("<", ``$< : int -> int -> bool``),
                   ("<=", ``$<= : int -> int -> bool``),
                   (">", ``$> : int -> int -> bool``),
                   (">=", ``$>= : int -> int -> bool``),
                   (GrammarSpecials.fromNum_str, ``int_of_num``),
                   (GrammarSpecials.num_injection, ``int_of_num``)];

fun deprecate_int () = let
  fun losety {Name,Thy,Ty} = {Name = Name, Thy = Thy}
  fun doit (s, t) = Parse.temp_remove_ovl_mapping s (losety (dest_thy_const t))
in
  app (ignore o doit) operators
end

fun prefer_int () = app Parse.temp_overload_on operators

val ARITH_CONV = Omega.OMEGA_CONV
val ARITH_TAC = Omega.OMEGA_TAC
val ARITH_PROVE = Omega.OMEGA_PROVE

val _ = if !Globals.interactive then
          Feedback.HOL_MESG ("intLib loaded.  Use intLib.deprecate_int()"^
                             " to turn off integer parsing")
        else ()

end;
