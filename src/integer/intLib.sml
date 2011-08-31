structure intLib :> intLib =
struct

  open HolKernel Abbrev intSimps Cooper

  val operators = [("+", intSyntax.plus_tm),
                   ("-", intSyntax.minus_tm),
                   ("numeric_negate", intSyntax.negate_tm),
                   ("*", intSyntax.mult_tm),
                   ("/", intSyntax.div_tm),
                   ("<", intSyntax.less_tm),
                   ("<=", intSyntax.leq_tm),
                   (">", intSyntax.great_tm),
                   (">=", intSyntax.geq_tm),
                   (GrammarSpecials.fromNum_str, intSyntax.int_injection),
                   (GrammarSpecials.num_injection, intSyntax.int_injection)];

fun deprecate_int () = let
  fun doit (s, t) =
     let val {Name,Thy,...} = dest_thy_const t in
        Parse.temp_send_to_back_overload s {Name = Name, Thy = Thy}
     end
in
  List.app doit operators
end

fun prefer_int () = let
  fun doit (s, t) =
     let val {Name,Thy,...} = dest_thy_const t in
        Parse.temp_bring_to_front_overload s {Name = Name, Thy = Thy}
     end
in
  List.app doit operators
end

val ARITH_CONV = Omega.OMEGA_CONV
val ARITH_TAC = Omega.OMEGA_TAC
val ARITH_PROVE = Omega.OMEGA_PROVE

val _ = if !Globals.interactive then
          Feedback.HOL_MESG ("intLib loaded.  Use intLib.deprecate_int()"^
                             " to turn off integer parsing")
        else ()

end;
