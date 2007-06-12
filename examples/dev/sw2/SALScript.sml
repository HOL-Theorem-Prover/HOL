(*---------------------------------------------------------------------------*)
(* SAL - Structured Assembly Language                                        *)
(*---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "SAL";

(*---------------------------------------------------------------------------*)
(* Labels                                                                    *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype `LABEL = L of num`;

val inc_def = Define `inc (L i) = L (i + 1)`;

(*---------------------------------------------------------------------------*)
(* Tail Recursion                                                            *)
(*---------------------------------------------------------------------------*)

val tr_def =
 TotalDefn.DefineSchema
   `tr (x:'a) = if f1 x then x else tr (f2 x)`;

val tr_ind = fetch "-" "tr_ind";

val tr_INTRO = Q.store_thm
("tr_INTRO",
  `!f f1 f2.
     (!x:'a. f x = if f1(x) then x else f(f2 x))
     ==> (?R. WF R /\ (!x. ~f1 x ==> R (f2 x) x))
     ==> (f:'a->'a = tr f1 f2)`,

  REPEAT (GEN_TAC ORELSE STRIP_TAC) THEN
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
  HO_MATCH_MP_TAC tr_ind THEN
  GEN_TAC THEN STRIP_TAC THEN
  IMP_RES_TAC (DISCH_ALL tr_def) THEN
  POP_ASSUM (fn th => ONCE_REWRITE_TAC[th]) THEN
  METIS_TAC[]
 );

val rec_INTRO = Q.store_thm
("rec_INTRO",
  `!f f1 f2 f3.
     (!x:'a. f x = if f1(x) then f2(x) else f(f3 x))
     ==> (?R. WF R /\ (!x. ~f1 x ==> R (f3 x) x))
     ==> (f:'a->'b x = let y = (tr f1 f3) x in f2 y)`,

  REPEAT (GEN_TAC ORELSE STRIP_TAC) THEN
  IMP_RES_TAC  relationTheory.WF_INDUCTION_THM THEN
  POP_ASSUM (MATCH_MP_TAC o SIMP_RULE std_ss [] o
          Q.SPEC `\x. f x = let y = (tr f1 f3) x in f2 y`) THEN
  REPEAT STRIP_TAC THEN
  Cases_on `f1 x` THENL [
    METIS_TAC [DISCH_ALL tr_def],
    IMP_RES_TAC (DISCH_ALL tr_def) THEN
    METIS_TAC []
  ]
 );

(*---------------------------------------------------------------------------*)
(* Structured Assembly Language                                              *)
(* Syntax                                                                    *)
(*---------------------------------------------------------------------------*)

val _ = 
 Hol_datatype 
   `COMPOSITE 
      = ASG of LABEL => 'a => 'a  => LABEL
      | IFGOTO of LABEL => ('a -> bool) => LABEL => LABEL
      | GOTO of LABEL => LABEL
      | UNION of COMPOSITE => COMPOSITE`;

val _ = overload_on ("|+", Term`UNION`);
val _ = set_fixity "|+" (Infixl 650);

(*---------------------------------------------------------------------------*)
(* Abstract Assembly Language                                                *)
(* Natural Operational Semantics                                             *)
(*---------------------------------------------------------------------------*)

(*  Values:                      *) 
(*     NIL -- (w,w) or ()        *)
(*     VAL -- (w,v)              *)

(* Natural semantics represented by reduction rules *)

val (ns_rule, ns_ind, ns_case) =
    Hol_reln `

    (Reduce (l1, ASG l1 v w l2, l2) (w,v)) /\                                  (* inst *)

    (Reduce (l1, S1, l2) (v,v) /\ Reduce (l2, S2, l3) value ==>                (* nop *)
       Reduce (l1, S1 |+ S2, l3) value) /\

    (Reduce (l1, S1, l2) e1 /\ Reduce (l3, S2, l4) e2 ==>                      (* skip *)
       Reduce (l1, S1 |+ S2, l2) e1) /\

    (Reduce (l1, S1, l2) (e,v) /\ Reduce (l2, S2, l3) (f v, w) ==> (* seq *)
       Reduce (l1, S1 |+ S2, l3) ((let v = e in f v), w)) /\

    (c v ==> Reduce (l1, IFGOTO l1 c l2 l3, l2) (v,v)) /\                      (* ift *)

    (~c v ==> Reduce (l1, IFGOTO l1 c l2 l3, l3) (v,v)) /\                     (* iff *)

    (Reduce (l1, GOTO l1 l2, l2) (v,v)) /\                                     (* goto *)

    (Reduce (l1, S1, l1) (g v, v) /\ Reduce (l1, S1, l2) (f (g v), (g v)) ==>  (* loop *)
       Reduce (l1, S1, l2) (f v, v))
  `;

(*
val _ = Hol_datatype `
     VALUE = 
           NIL
        |  VAL of num # num`;

    (Reduce (l1, S1, l1) v ==>                                               (* union *)
       Reduce (l1, S1 |+ S1, l1) v)           /\
    (Reduce (l1, S1, l2) (VAL(f v, v)) ==>                                   (* args *)
       Reduce (l1, S1, l2) (VAL(f (g v), g v)))  /\
*)

val [inst_rule, nop_rule, skip_rule, seq_rule, 
     ift_rule, iff_rule, goto_rule, loop_rule] = CONJUNCTS ns_rule;

val _ = map save_thm
  [("inst_rule",inst_rule), ("nop_rule",nop_rule), 
   ("skip_rule",skip_rule), ("seq_rule",seq_rule), 
   ("ift_rule",ift_rule),   ("iff_rule",iff_rule), 
   ("goto_rule",goto_rule), ("loop_rule",loop_rule)];


(* TRANSFER_RULE is a special case of the seq_rule *)
val TRANSFER_RULE = Q.store_thm (
  "TRANSFER_RULE",
   `Reduce (l1,S1,l2) (e,v) /\ Reduce (l2,S2,l3) (v,w) ==>
         Reduce (l1,S1 |+ S2,l3) (e,w)
   `,
   REPEAT STRIP_TAC THEN
   `Reduce (l2,S2,l3) ((\x.x) v, w)` by RW_TAC std_ss [] THEN
   IMP_RES_TAC seq_rule THEN
   FULL_SIMP_TAC std_ss [LET_THM]
  );

(*---------------------------------------------------------------------------*)
(* Translate conditional-jump structures into structured assembly            *)
(*---------------------------------------------------------------------------*)

val CONDITIONAL_RULE = Q.store_thm (
  "CONDITIONAL_RULE",
   `Reduce (l2, S1, l4) (e1 v, v) /\ Reduce (l3, S2, l4) (e2 v, v) ==>
    Reduce (l1, (IFGOTO l1 c l2 l3) |+ S1 |+ S2, l4) (if c v then e1 v else e2 v, v)`,
   Cases_on `c v` THEN
   RW_TAC std_ss [] THENL [
       METIS_TAC [ift_rule, nop_rule, skip_rule],
       METIS_TAC [iff_rule, nop_rule, skip_rule]
   ]
  );

(*---------------------------------------------------------------------------*)
(* The basic theorem for translating recursive structures into               *)
(* structured assembly                                                       *)
(*---------------------------------------------------------------------------*)

(* lem1 (rule tr, page 12) in the CADE paper *)
val TR_LEM1 = Q.store_thm (
  "TR_LEM1",
   `Reduce (l3, S1, l4) w /\ c v ==>
    Reduce (l1, (IFGOTO l1 c l2 l3) |+ S1 |+ (GOTO l4 l1), l2) (v,v)`,

  REPEAT STRIP_TAC THEN
  METIS_TAC [ift_rule, skip_rule, goto_rule]
  );

(* thm1 (rule tr, page 12) in the CADE paper *)
val TR_LEM2 = Q.store_thm (
  "TR_LEM2",
   `(!x. ~(c x) ==> R (f x) x) /\ WF R /\       (* terminated loop *)
    c v /\ Reduce (l3, S1, l4) (f v, v) 
    ==>
    Reduce (l1, (IFGOTO l1 c l2 l3) |+ S1 |+ (GOTO l4 l1), l2)
        (tr c f v, v)`,

  RW_TAC std_ss [] THEN
  METIS_TAC[TR_LEM1, DISCH_ALL tr_def]
  );

(* asm4 (rule tr, page 12) in the CADE paper is the assumption when applying the tr_ind *)

(* asm5 (rule tr, page 12) in the CADE paper *)
val TR_LEM3 = Q.store_thm (
  "TR_LEM3",
   `~c v /\ Reduce (l3, S1, l4) (f v, v)  ==>
    Reduce (l1, (IFGOTO l1 c l2 l3) |+ S1 |+ (GOTO l4 l1), l1) (f v, v)`,

  RW_TAC std_ss [] THEN
  `Reduce (l1, (IFGOTO l1 c l2 l3) |+ S1, l4) (f v, v)` by METIS_TAC [iff_rule, nop_rule] THEN
  METIS_TAC [goto_rule, TRANSFER_RULE]
  );

val TR_RULE = Q.store_thm (
   "TR_RULE",
   `(!x. ~(c x) ==> R (f x) x) /\ WF R ==>
    (!v. (c v ==> Reduce (l3, S1, l4) w) /\
         (~c v ==> Reduce (l3, S1, l4) (f v, v))) ==>
        !v. Reduce (l1, (IFGOTO l1 c l2 l3) |+ S1 |+ (GOTO l4 l1), l2) (tr c f v, v)`,

  STRIP_TAC THEN STRIP_TAC THEN
  IMP_RES_TAC (DISCH_ALL tr_ind) THEN
  POP_ASSUM HO_MATCH_MP_TAC THEN
  RW_TAC std_ss [] THEN
  Cases_on `c v` THENL [
    METIS_TAC [TR_LEM1, DISCH_ALL tr_def],
    METIS_TAC [TR_LEM3, loop_rule]
  ]
  );

(*---------------------------------------------------------------------------*)
(* The basic theorem for translating function call structures into           *)
(* structured assembly                                                       *)
(*---------------------------------------------------------------------------*)

val FUN_CALL_LEM = Q.store_thm (
  "FUN_CALL_LEM",
   `Reduce (l2, S1, l3) (f w1, v1) ==>
    Reduce (l1, (ASG l1 w1 w2 l2) |+ S1, l3) ((let w1 = w2 in f w1), v1)`,

   RW_TAC std_ss [] THEN
   METIS_TAC [inst_rule, seq_rule]
  );

val FUN_CALL_RULE = Q.store_thm (
  "FUN_CALL_RULE",
   `Reduce (l2, S1, l3) (f w1, v1) ==>
    Reduce (l1, (ASG l1 w1 w2 l2) |+ S1 |+ (ASG l3 v2 v1 l4), l4) (f w2, v2)`,

   RW_TAC std_ss [] THEN
   IMP_RES_TAC FUN_CALL_LEM THEN
   FULL_SIMP_TAC std_ss [LET_THM] THEN
   `Reduce (l3,ASG l3 v2 v1 l4,l4) ((\x.x) v1, v2)` by SIMP_TAC std_ss [inst_rule] THEN
   Q.PAT_ASSUM `!w2 l1.P` (ASSUME_TAC o Q.SPECL [`w2`,`l1`]) THEN
   IMP_RES_TAC seq_rule THEN
   FULL_SIMP_TAC std_ss [LET_THM]
  );

val _ = export_theory();

(*---------------------------------------------------------------------------*)
(* Examples                                                                  *)
(*---------------------------------------------------------------------------*)

(* 
val f_def = Define `f x = 
         if x = 0 then x else x + f (x - 1)`;

val f = ``\f x. if x = 0 then x else x + f (x - 1)``;
val f' = ``(\f x. if x = 0 then x else x + f (x - 1)) f x``;

*)

