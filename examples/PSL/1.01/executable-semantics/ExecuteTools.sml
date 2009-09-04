(*****************************************************************************)
(* Executing the Sugar2 semantics                                            *)
(*****************************************************************************)

structure ExecuteTools :> ExecuteTools =
struct

(*
quietdec := true;
loadPath := "../official-semantics"   ::
            "../executable-semantics" ::
            "../regexp"               ::
            !loadPath;
map load
 ["bossLib", "metisLib", "matcherTheory", "KripkeTheory", "UnclockedSemanticsTheory",
  "SyntacticSugarTheory", "ClockedSemanticsTheory", "RewritesTheory",
  "rich_listTheory", "intLib", "res_quanLib", "res_quanTheory"];
open KripkeTheory FinitePathTheory PathTheory SyntaxTheory SyntacticSugarTheory
     UnclockedSemanticsTheory ClockedSemanticsTheory RewritesTheory
     arithmeticTheory listTheory rich_listTheory res_quanLib res_quanTheory
     ClockedSemanticsTheory metisLib matcherTheory;
val _ = intLib.deprecate_int();
quietdec := false;
*)

open HolKernel Parse boolLib;
open bossLib metisLib pairTheory combinTheory listTheory rich_listTheory
     pred_setTheory arithmeticTheory;
open regexpLib SyntaxTheory UnclockedSemanticsTheory PropertiesTheory
     ExecuteSemanticsTheory;

(******************************************************************************
* Evaluating expressions of the form x IN {y1; y2; ...; yn}
******************************************************************************)

(* For the current set of Sugar2 example properties, the following INSERT
   theorems seem to work better than this general conversion.
val _ =
 computeLib.add_convs
  [(``$IN``,
    2,
    (pred_setLib.SET_SPEC_CONV ORELSEC pred_setLib.IN_CONV EVAL))];
*)

val () = computeLib.add_funs
  [pred_setTheory.IN_INSERT,
   pred_setTheory.NOT_IN_EMPTY];

(******************************************************************************
* Evaluating Sugar2 formulas
******************************************************************************)
val _ = computeLib.add_funs
  [PathTheory.SEL_REC_AUX,
   UF_SEM_F_UNTIL_REC,
   B_SEM,
(* Prefer the optimizing version of
   EVAL_US_SEM,
*)
   EVAL_UF_SEM_F_SUFFIX_IMP,
   EVAL_UF_SEM_F_WEAK_IMP,
   UF_SEM_F_STRONG_IMP_F_SUFFIX_IMP,
   S_CLOCK_COMP_ELIM,
   F_TRUE_CLOCK_COMP_ELIM];

(******************************************************************************
* For simplification during symbolic evaluation of Sugar2 formulas
******************************************************************************)

(* Rejected by computeLib.add_funs, but (used to be) useful for simplification.
val SOME_EL_F =
 prove
  (``SOME_EL (\x. F) l = F``,
   Induct_on `l`
    THEN RW_TAC std_ss [SOME_EL]);
*)

val EXISTS_COND = prove
  (``!p c a b.
       EXISTS p (if c then a else b) = if c then EXISTS p a else EXISTS p b``,
   RW_TAC std_ss []);

val COND_SIMP = prove
  (``!c a b.
       (COND c a F = c /\ a) /\ (COND c a T = ~c \/ a) /\
       (COND c T b = c \/ b) /\ (COND c F b = ~c /\ b)``,
   RW_TAC std_ss [IMP_DISJ_THM]);

val () = computeLib.add_funs
  [EXISTS_COND,
   COND_SIMP,
   DECIDE ``SUC n > 0 = T``];

(*---------------------------------------------------------------------------*)
(* Executing the US_SEM optimizer.                                           *)
(*---------------------------------------------------------------------------*)

val US_SEM_tm = ``US_SEM : ('a -> bool) list -> 'a sere -> bool``;

val S_REPEAT_IDEMPOTENT1 = prove
  (``!w r x.
       US_SEM w (S_CAT (S_REPEAT r, S_CAT (S_REPEAT r, x))) =
       US_SEM w (S_CAT (S_REPEAT r, x))``,
   REWRITE_TAC [GSYM S_CAT_ASSOC]
   THEN ONCE_REWRITE_TAC [US_SEM_def]
   THEN REWRITE_TAC [S_REPEAT_IDEMPOTENT]);

val US_SEM_conv =
  REWRITE_CONV [S_CAT_ASSOC, S_REPEAT_IDEMPOTENT, S_REPEAT_IDEMPOTENT1]
  THENC REWR_CONV EVAL_US_SEM
  THENC EVAL;

val () = computeLib.add_convs [(US_SEM_tm, 2, US_SEM_conv)];

end
