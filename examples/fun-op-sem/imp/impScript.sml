
open HolKernel Parse boolLib bossLib;
open stringLib integerTheory;
val ect = BasicProvers.EVERY_CASE_TAC;

val _ = new_theory "imp";

(*

This file defines a funcional big-step semantics for the IMP languages
of Nipkow and Klein's book Concrete Semantics.

http://www.concrete-semantics.org/

*)

val _ = temp_type_abbrev("vname",``:string``);

val _ = Datatype `
  aexp = N int | V vname | Plus aexp aexp`;

val _ = Datatype `
  bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp`;

val _ = Datatype `
  com = SKIP
      | Assign vname aexp
      | Seq com com
      | If bexp com com
      | While bexp com`

val aval_def = Define `
  (aval (N n) s = n) /\
  (aval (V x) s = s x) /\
  (aval (Plus a1 a2) s = aval a1 s + aval a2 s)`;

val bval_def = Define `
  (bval (Bc v) s = v) /\
  (bval (Not b) s = ~bval b s) /\
  (bval (And b1 b2) s = (bval b1 s /\ bval b2 s)) /\
  (bval (Less a1 a2) s = (aval a1 s < aval a2 s))`;

val STOP_def = Define `STOP x = x`;

(* The following function defines the semantics of statement evaluation.
   The clock decreases when entering the body of the While loop.

   NB: the definition mechanism in HOL4 is not smart enough to notice
   that the clock doesn't increase. In order to make the termination
   simple, we insert an extra `if t < t2 then t else t2` in the Seq
   case. In cval_def_with_stop below, we remove this redundant
   if-statement. *)

Definition cval_def:
  (cval SKIP s (t:num) = SOME (s,t)) /\
  (cval (Assign x a) s t = SOME ((x =+ aval a s) s,t)) /\
  (cval (Seq c1 c2) s t =
    case cval c1 s t of
    | NONE => NONE
    | SOME (s2,t2) => cval c2 s2 (if t < t2 then t else t2)) /\
  (cval (If b c1 c2) s t =
    cval (if bval b s then c1 else c2) s t) /\
  (cval (While b c) s t =
    if bval b s then
      if t = 0 then NONE else cval (Seq c (STOP (While b c))) s (t - 1)
    else SOME (s,t))
Termination
  WF_REL_TAC `inv_image (measure I LEX measure com_size)
                            (λ(c,s,t). (t,c))`
  \\ SRW_TAC [] [] \\ DECIDE_TAC
End

val clock_bound = prove(
  ``!c s t s' t'. (cval c s t = SOME (s',t')) ==> t' <= t``,
  recInduct (theorem "cval_ind") \\ rpt strip_tac
  \\ fs [cval_def] \\ ect \\ fs [] \\ decide_tac);

fun term_rewrite tms = let
  fun f tm = ASSUME (list_mk_forall(free_vars tm,tm))
  in rand o concl o QCONV (REWRITE_CONV (map f tms)) end

val r = term_rewrite [``(if t < t2 then t else t2) = t2:num``];

val cval_def_with_stop = store_thm("cval_def_with_stop",
  cval_def |> concl |> r,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [Once cval_def]
  \\ ect \\ imp_res_tac clock_bound \\ `r = t` by DECIDE_TAC \\ fs []);

Theorem cval_def[allow_rebind] =
        REWRITE_RULE [STOP_def] cval_def_with_stop

(* We also remove the redundant if-statement from the induction theorem. *)

val cval_ind = prove(
  cval_ind |> concl |> r,
  NTAC 2 STRIP_TAC \\ HO_MATCH_MP_TAC (theorem "cval_ind")
  \\ REPEAT STRIP_TAC \\ fs []
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs []
  \\ REPEAT STRIP_TAC \\ fs [STOP_def]
  \\ RES_TAC \\ imp_res_tac clock_bound
  \\ Cases_on `t < t2` \\ fs []
  \\ `t = t2` by DECIDE_TAC \\ fs []) |> REWRITE_RULE [STOP_def];

Theorem cval_ind[allow_rebind] = cval_ind

val _ = export_theory();
