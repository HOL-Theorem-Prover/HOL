structure intLib :> intLib =
struct

  open HolKernel Abbrev intSimps Cooper

  val operators = [("+", intSyntax.plus_tm),
                   ("-", intSyntax.minus_tm),
                   ("*", intSyntax.mult_tm),
                   ("/", intSyntax.div_tm),
                   ("<", intSyntax.less_tm),
                   ("<=", intSyntax.leq_tm),
                   (">", intSyntax.great_tm),
                   (">=", intSyntax.geq_tm),
                   (GrammarSpecials.fromNum_str, intSyntax.int_injection),
                   (GrammarSpecials.num_injection, intSyntax.int_injection)];

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
