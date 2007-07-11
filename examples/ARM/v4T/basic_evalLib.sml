(* ========================================================================= *)
(* FILE          : basic_evalLib.sml                                         *)
(* DESCRIPTION   : Code for basic evaluation of the ARM specification        *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2006                                                      *)
(* ========================================================================= *)

structure basic_evalLib :> basic_evalLib =
struct

(* interactive use:
  app load ["systemTheory", "instructionTheory", "wordsLib"];
*)

open HolKernel boolLib bossLib systemTheory instructionTheory wordsLib;

(* ------------------------------------------------------------------------- *)
(* Running the model *)

fun eval (t, m, r, s) = EVAL (subst
  [``mem:mem`` |-> m, ``registers:registers`` |-> r, ``psrs:psrs`` |-> s,
   ``t:num`` |-> (numLib.mk_numeral o Arbnum.fromInt) t]
   ``STATE_ARM_SYS TRANSFERS NO_CP t
       <| registers := registers; psrs :=  psrs;
          memory := mem; undefined := F; cp_state := () |>``);

(* ------------------------------------------------------------------------- *)

end
