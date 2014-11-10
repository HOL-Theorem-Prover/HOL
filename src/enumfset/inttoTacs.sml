(* File: inttoTacs.sml. Author: F. Lockwood Morris. Split off from        *)
(* totoTacs 12/13/13 -- see inttoScript.sml. *)

structure inttoTacs :> inttoTacs =
struct
(*
app load ["totoTheory", "totoTacs", "inttoTheory", "intLib"];
*)
open Parse HolKernel boolLib bossLib;

val _ = set_trace "Unicode" 0;
open totoTheory totoTacs inttoTheory intLib;

val AR = ASM_REWRITE_TAC [];
fun ulist x = [x];

val ERR = mk_HOL_ERR "inttoTacs";

val _ = intLib.deprecate_int ();

(* ****************************************************************** *)
(*                           intto_CONV                               *)
(* ****************************************************************** *)

(* integer parsing remains deprecated; note use of suffix i below. *)

(* An integer ground term is, as well as I can see, either a application of
   ``$&`` to a num ground term (which is either ``0`` or an application
   of NUMERAL to a pile of ZERO, BIT0, and BIT1) or an application of
   numeric_negate:int -> int to such a &-application. ``-0`` is considered
   possible, but if it never occurs, then one of the first two REWR_CONV's
   in each list of five for different signs will succeed. *)

fun intOrd_CONV t =
let val (l, r) = (rand (rator t), rand t)
in if rator l = ``numeric_negate``
   then if rator r = ``numeric_negate``
        then (REWR_CONV neg_neg_thm THENC numOrd_CONV) t
        else (FORK_CONV
              (RAND_CONV (RAND_CONV num_pre_CONV), RAND_CONV num_pre_CONV) THENC
              (REWR_CONV neg_BIT1_lt_thm ORELSEC
               REWR_CONV neg_BIT2_lt_thm ORELSEC
               REWR_CONV neg_lt_BIT1_thm ORELSEC
               REWR_CONV neg_lt_BIT2_thm ORELSEC
               REWR_CONV neg_ZERO_eq_ZERO_thm)) t
   else if rator r = ``numeric_negate``
        then (FORK_CONV
              (RAND_CONV num_pre_CONV, RAND_CONV (RAND_CONV num_pre_CONV)) THENC
              (REWR_CONV gt_neg_BIT1_thm ORELSEC
               REWR_CONV gt_neg_BIT2_thm ORELSEC
               REWR_CONV BIT1_gt_neg_thm ORELSEC
               REWR_CONV BIT2_gt_neg_thm ORELSEC
               REWR_CONV ZERO_eq_neg_ZERO_thm)) t
        else (REWR_CONV pos_pos_thm THENC numOrd_CONV) t
end;

(* map intOrd_CONV
 [``intOrd (-2i) (-3i)``, ``intOrd (-2i) 3i``, ``intOrd (-2i) 2i``,
  ``intOrd (-2i) 0i``, ``intOrd (-3i) 0i``, ``intOrd (-0i) 0i``,
  ``intOrd 2i 3i``, ``intOrd 2i (-3i)``, ``intOrd 3i (-3i)``,
  ``intOrd 0i (-2i)``, ``intOrd (0i) (-3i)``, ``intOrd 0i (-0i)``]; *)

val intto_CONV = 
RATOR_CONV (RATOR_CONV (REWR_CONV apintto_thm)) THENC
                 intOrd_CONV;

(* map intto_CONV
 [``apto intto (-2i) (-3i)``, ``apto intto (-2i) 3i``, ``apto intto (-2i) 2i``,
  ``apto intto (-2i) 0i``, ``apto intto (-3i) 0i``, ``apto intto (-0i) 0i``,
  ``apto intto 2i 3i``, ``apto intto 2i (-3i)``, ``apto intto 3i (-3i)``,
``apto intto 0i (-2i)``, ``apto intto (0i) (-3i)``, ``apto intto 0i (-0i)``];*)

end;
