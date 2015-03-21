
open HolKernel Parse boolLib bossLib;
open stringLib integerTheory;
open lcsymtacs;
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
  (bval (And b1 b2) s = bval b1 s /\ bval b2 s) /\
  (bval (Less a1 a2) s = aval a1 s < aval a2 s)`;

val STOP_def = Define `STOP x = x`;

(* The following function defines the semantics of statement evaluation.
   The clock decreases when entering the body of the While loop.

   NB: the definition mechanism in HOL4 is not smart enough to notice
   that the clock doesn't increase. In order to make the termination
   simple, we insert an extra `if t < t2 then t else t2` in the Seq
   case. In cval_def_with_stop below, we remove this redundant
   if-statement. *)

val cval_def = tDefine "cval" `
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
    else SOME (s,t))`
 (WF_REL_TAC `inv_image (measure I LEX measure com_size)
                            (\(c,s,t). (t,c))`
  \\ SRW_TAC [] [] \\ DECIDE_TAC)

val clock_bound = prove(
  ``!c s t s' t'. (cval c s t = SOME (s',t')) ==> t' <= t``,
  recInduct (theorem "cval_ind")
  \\ REPEAT STRIP_TAC
  \\ fs [cval_def]
  \\ ect \\ fs []
  \\ DECIDE_TAC);

val cval_def_with_stop = store_thm("cval_def_with_stop",
  ``(cval SKIP s (t:num) = SOME (s,t)) /\
    (cval (Assign x a) s t = SOME ((x =+ aval a s) s,t)) /\
    (cval (Seq c1 c2) s t =
      case cval c1 s t of
      | NONE => NONE
      | SOME (s2,t2) => cval c2 s2 t2) /\
    (cval (If b c1 c2) s t =
      cval (if bval b s then c1 else c2) s t) /\
    (cval (While b c) s t =
      if bval b s then
        if t = 0 then NONE else cval (Seq c (STOP (While b c))) s (t - 1)
      else SOME (s,t))``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [Once cval_def]
  \\ ect \\ imp_res_tac clock_bound \\ `r = t` by DECIDE_TAC \\ fs []);

val cval_def =
  save_thm("cval_def",REWRITE_RULE [STOP_def] cval_def_with_stop);

(* We also remove the redundant if-statement from the induction theorem. *)

val cval_ind = store_thm("cval_ind",
  ``!P.
      (!s t. P SKIP s t) /\ (!x a s t. P (Assign x a) s t) /\
      (!c1 c2 s t.
         (!v s2 t2.
            (cval c1 s t = SOME v) /\ (v = (s2,t2)) ==> P c2 s2 t2) /\
            P c1 s t ==>
         P (Seq c1 c2) s t) /\
      (!b c1 c2 s t.
         P (if bval b s then c1 else c2) s t ==> P (If b c1 c2) s t) /\
      (!b c s t.
         (bval b s /\ t <> 0 ==>
          P (Seq c (While b c)) s (t - 1)) ==>
         P (While b c) s t) ==>
      !v v1 v2. P v v1 v2``,
  NTAC 2 STRIP_TAC \\ HO_MATCH_MP_TAC (theorem "cval_ind")
  \\ REPEAT STRIP_TAC \\ fs []
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs []
  \\ REPEAT STRIP_TAC \\ fs [STOP_def]
  \\ RES_TAC \\ imp_res_tac clock_bound
  \\ Cases_on `t < t2` \\ fs []
  \\ `t = t2` by DECIDE_TAC \\ fs []);

val _ = export_theory();
