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
  val deprecate_real = realSyntax.deprecate_real
  val prefer_real = realSyntax.prefer_real

  (* The default REAL_ARITH, etc. can be switched here. *)
  val REAL_ARITH_TAC     = TRY(RealArith.OLD_REAL_ARITH_TAC)
                           THEN RealField.REAL_ARITH_TAC;

  fun REAL_ARITH tm      = RealArith.OLD_REAL_ARITH tm
                           handle HOL_ERR _ => RealField.REAL_ARITH tm;

  val REAL_ASM_ARITH_TAC = TRY(RealArith.OLD_REAL_ASM_ARITH_TAC)
                           THEN RealField.REAL_ASM_ARITH_TAC;

 (* NOTE: The PURE_REAL_ARITH_TAC exported by realLib is always the old one *)
end
