(* ========================================================================= *)
(* FILE          : hhExportLib.sml                                           *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(*                     Cezary Kaliszyk, University of Innsbruck              *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure hhExportLib :> hhExportLib =
struct

open HolKernel boolLib aiLib hhTranslate

(* -------------------------------------------------------------------------
   Writer shortcuts
   ------------------------------------------------------------------------- *)

fun os oc s = TextIO.output (oc,s)

fun oiter_aux oc sep f l = case l of
    []     => ()
  | [a]    => f oc a
  | a :: m => (f oc a; os oc sep; oiter_aux oc sep f m)

fun oiter oc sep f l = oiter_aux oc sep f l

end (* struct *)
