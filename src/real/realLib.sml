(* ========================================================================= *)
(* Bring in the entire development, from definition of real numbers,         *)
(* through transcendentals, with polynomials too. Linear decision procedure  *)
(* is also included. plus some other proof procedures.                       *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*                                                                           *)
(*       Ported to hol98 by Joe Hurd, 2 Oct 1998                             *)
(* ========================================================================= *)

structure realLib :> realLib =
struct
  open HolKernel realSimps RealArith RealField isqrtLib Tactical;

  val operators = [("+", realSyntax.plus_tm),
                   ("-", realSyntax.minus_tm),
                   ("~", realSyntax.negate_tm),
                   ("numeric_negate", realSyntax.negate_tm),
                   ("*", realSyntax.mult_tm),
                   ("/", realSyntax.div_tm),
                   ("<", realSyntax.less_tm),
                   ("<=", realSyntax.leq_tm),
                   (">", realSyntax.greater_tm),
                   (">=", realSyntax.geq_tm),
                   (GrammarSpecials.fromNum_str, realSyntax.real_injection),
                   (GrammarSpecials.num_injection, realSyntax.real_injection)];

  fun deprecate_real () = let
    fun doit (s, t) =
       let val {Name,Thy,...} = dest_thy_const t in
          Parse.temp_send_to_back_overload s {Name = Name, Thy = Thy}
       end
  in
    List.app doit operators
  end

  fun prefer_real () = let
    fun doit (s, t) =
       let val {Name,Thy,...} = dest_thy_const t in
          Parse.temp_bring_to_front_overload s {Name = Name, Thy = Thy}
       end
  in
    List.app doit operators
  end

  val REAL_ARITH_TAC     = RealField.REAL_ARITH_TAC;
  val REAL_ARITH         = RealField.REAL_ARITH;
  val REAL_ASM_ARITH_TAC = RealField.REAL_ASM_ARITH_TAC;

end
