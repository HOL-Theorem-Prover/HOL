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
  type conv = Abbrev.conv

  local open transcTheory in end;

  open RealArith realSimps Diff isqrtLib;

end
