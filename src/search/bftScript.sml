(*---------------------------------------------------------------------------*)
(* Breadth-first traversal of directed graphs that can contain cycles.       *)
(*---------------------------------------------------------------------------*)

open HolKernel boolLib bossLib
     pred_setTheory pred_setLib relationTheory listTheory
     dirGraphTheory;

val set_ss = list_ss ++ PRED_SET_ss;
val dnf_ss = bool_ss ++ boolSimps.DNF_ss ++ rewrites [AND_IMP_INTRO];

val _ = new_theory "bft";

(*---------------------------------------------------------------------------*)
(* BFT :('a -> 'a list) ->   (* graph *)                                     *)
(*      ('a -> 'b -> 'b) ->  (* folding function *)                          *)
(*      'a list ->           (* nodes seen *)                                *)
(*      'a list ->           (* fringe to visit *)                           *)
(*      'b ->                (* accumulator *)                               *)
(*      'b                   (* final result *)                              *)
(*                                                                           *)
(* BFT checks that the given graph has finite Parents.  If the Parents set   *)
(* is finite then the graph has only finitely many edges (because G produces *)
(* a list of children, a node has only finitely many children) and DFT must  *)
(* terminate.                                                                *)
(*                                                                           *)
(* Termination proof. In the first recursive call, the fringe list is        *)
(* shorter. In the second recursive call, the seen and fringe argument can   *)
(* both increase, but in different circumstances.  In this call, h has not   *)
(* been seen.  If it is a parent in the graph, then adding it to seen        *)
(* decreases the number of unseen parents in the graph. If it is not a       *)
(* parent, then it has no children, and so the fringe list shrinks.          *)
(*---------------------------------------------------------------------------*)

val Rel_def =   (* map arg. tuples into a pair of numbers for termination *)
 Define
   `Rel(G,f,seen,fringe,acc) =
        (CARD(Parents G DIFF (LIST_TO_SET seen)), LENGTH fringe)`;

val () = computeLib.auto_import_definitions := false

Definition BFT_def0[induction=BFT_ind0]:
  BFT G f seen fringe acc =
    if FINITE (Parents G)
      then case fringe
           of [] => acc
           | h::t =>
              if MEM h seen
                then BFT G f seen t acc
                else BFT G f (h::seen)
                             (t ++ G h)
                             (f h acc)
      else ARB
Termination
 WF_REL_TAC `inv_image ($< LEX $<) Rel`
   THEN RW_TAC set_ss [Rel_def, DECIDE ``(0 < p - q) <=> q < p ``]
   THEN Cases_on `h IN Parents G` THENL
   [DISJ1_TAC, DISJ2_TAC] THEN RW_TAC set_ss [] THENL
   [MATCH_MP_TAC (DECIDE ``y <= x /\ y < z ==> x < z + (x - y)``) THEN
     CONJ_TAC THENL
      [METIS_TAC [CARD_INTER_LESS_EQ],
       MATCH_MP_TAC (SIMP_RULE dnf_ss [] CARD_PSUBSET)
         THEN RW_TAC set_ss [INTER_DEF,PSUBSET_DEF,SUBSET_DEF,EXTENSION]
         THEN METIS_TAC[]],
    MATCH_MP_TAC (SIMP_RULE dnf_ss [] CARD_PSUBSET)
       THEN RW_TAC set_ss [INTER_DEF,PSUBSET_DEF,SUBSET_DEF,EXTENSION]
       THEN METIS_TAC[],
    MATCH_MP_TAC (DECIDE ``(p=q) ==> (x-p = x-q)``)
      THEN MATCH_MP_TAC (METIS_PROVE [] ``(s1=s2) ==> (CARD s1 = CARD s2)``)
      THEN RW_TAC set_ss [INTER_DEF,EXTENSION] THEN METIS_TAC [],
    FULL_SIMP_TAC set_ss [Parents_def]]
End

(*---------------------------------------------------------------------------*)
(* Desired recursion equations, constrained by finiteness of graph.          *)
(*---------------------------------------------------------------------------*)

val BFT_def = Q.store_thm
("BFT_def",
 `FINITE (Parents G) ==>
  (BFT G f seen [] acc = acc) /\
  (BFT G f seen (h :: t) acc =
    if MEM h seen
       then BFT G f seen t acc
       else BFT G f (h::seen)
                    (t ++ G h)
                    (f h acc))`,
 RW_TAC std_ss [] THENL
 [RW_TAC list_ss [BFT_def0],
  GEN_REWRITE_TAC LHS_CONV empty_rewrites [BFT_def0] THEN RW_TAC list_ss [],
  RW_TAC list_ss [BFT_def0],
  GEN_REWRITE_TAC LHS_CONV empty_rewrites [BFT_def0] THEN RW_TAC list_ss []]);

(*---------------------------------------------------------------------------*)
(* Desired induction theorem for BFT.                                        *)
(*---------------------------------------------------------------------------*)

val BFT_ind = Q.store_thm
("BFT_ind",
 `!P.
    (!G f seen h t acc.
       P G f seen [] acc /\
       ((FINITE (Parents G) /\ ~MEM h seen ==>
            P G f (h :: seen) (t ++ G h) (f h acc)) /\
        (FINITE (Parents G) /\ MEM h seen ==> P G f seen t acc)
         ==> P G f seen (h :: t) acc))
   ==>
   !v v1 v2 v3 v4. P v v1 v2 v3 v4`,
 NTAC 2 STRIP_TAC
 THEN HO_MATCH_MP_TAC BFT_ind0
 THEN REPEAT GEN_TAC THEN Cases_on `fringe`
 THEN RW_TAC list_ss []);

(*---------------------------------------------------------------------------*)
(* Basic lemmas about BFT                                                    *)
(*---------------------------------------------------------------------------*)

val BFT_CONS = Q.store_thm
("BFT_CONS",
 `!G f seen fringe acc a b.
    FINITE (Parents G) /\ (f = CONS) /\ (acc = APPEND a b)
      ==>
    (BFT G f seen fringe acc = BFT G f seen fringe a ++ b)`,
 recInduct BFT_ind
  THEN RW_TAC list_ss [BFT_def] THEN METIS_TAC [APPEND]);

val FOLDR_UNROLL = Q.prove
(`!f x b l. FOLDR f (f x b) l = FOLDR f b (l ++ [x])`,
 Induct_on `l` THEN RW_TAC list_ss []);

val BFT_FOLD = Q.store_thm
("BFT_FOLD",
 `!G f seen fringe acc.
    FINITE (Parents G)
       ==>
   (BFT G f seen fringe acc = FOLDR f acc (BFT G CONS seen fringe []))`,
 recInduct BFT_ind THEN
 RW_TAC list_ss [BFT_def] THEN METIS_TAC [FOLDR_UNROLL,BFT_CONS,APPEND]);

val BFT_ALL_DISTINCT_LEM = Q.prove
(`!G f seen fringe acc.
    FINITE (Parents G) /\ (f = CONS) /\
    ALL_DISTINCT acc /\ (!x. MEM x acc ==> MEM x seen)
      ==>
    ALL_DISTINCT (BFT G f seen fringe acc)`,
 recInduct BFT_ind THEN RW_TAC list_ss [BFT_def] THEN METIS_TAC []);

val BFT_ALL_DISTINCT = Q.store_thm
("BFT_ALL_DISTINCT",
 `!G seen fringe.
    FINITE (Parents G) ==> ALL_DISTINCT (BFT G CONS seen fringe [])`,
 RW_TAC list_ss [BFT_ALL_DISTINCT_LEM]);

(*---------------------------------------------------------------------------*)
(* If BFT visits x, then x is reachable or is in the starting accumulator    *)
(*---------------------------------------------------------------------------*)

val BFT_REACH_1 = Q.store_thm
("BFT_REACH_1",
 `!G f seen fringe acc.
    FINITE (Parents G) /\ (f = CONS) ==>
    !x. MEM x (BFT G f seen fringe acc) ==>
      x IN (REACH_LIST G fringe) \/ MEM x acc`,
 recInduct BFT_ind
 >> RW_TAC set_ss [BFT_def, REACH_LIST_def, REACH_def, IN_DEF]
    >- metis_tac []
    >- (rfs[]
        >> POP_ASSUM (MP_TAC o Q.SPEC `x`)
        >> RW_TAC set_ss []
           >- metis_tac[]
           >- (IMP_RES_TAC RTC_RULES >> metis_tac[])
           >- metis_tac[RTC_RULES]
           >- metis_tac[])
);

(*---------------------------------------------------------------------------*)
(* If x is reachable from fringe on a path that does not include the nodes   *)
(* in seen, then BFT visits x.                                               *)
(*---------------------------------------------------------------------------*)

val BFT_REACH_2 = Q.store_thm
("BFT_REACH_2",
 `!G f seen fringe acc x.
    FINITE (Parents G) /\ (f = CONS) /\
    x IN (REACH_LIST (EXCLUDE G (LIST_TO_SET seen)) fringe) /\
    ~MEM x seen
     ==>
      MEM x (BFT G f seen fringe acc)`,
 recInduct BFT_ind THEN RW_TAC set_ss [BFT_def] THENL
 [(* Base Case *)
  FULL_SIMP_TAC list_ss [IN_DEF, EXCLUDE_def, REACH_LIST_def],
  (* The head of fringe is in seen *)
  FULL_SIMP_TAC dnf_ss [SPECIFICATION, REACH_LIST_def]
  THEN RW_TAC list_ss [] THEN
  POP_ASSUM MP_TAC THEN RW_TAC list_ss [] THEN POP_ASSUM MATCH_MP_TAC THEN
  FULL_SIMP_TAC set_ss [SPECIFICATION, REACH_LIST_def] THENL
  [FULL_SIMP_TAC set_ss [REACH_EXCLUDE,Once RTC_CASES1,SPECIFICATION],ALL_TAC]
   THEN METIS_TAC [],
  (* The head of fringe is not in seen *)
  POP_ASSUM MP_TAC THEN RW_TAC set_ss [] THEN
    POP_ASSUM (MP_TAC o Q.SPEC `x`) THEN RW_TAC list_ss [] THEN
    Cases_on `x = h` THEN FULL_SIMP_TAC set_ss [] THEN
    RW_TAC set_ss [] THENL
    [RW_TAC list_ss [Q.SPECL [`G`, `CONS`, `h::seen`,
                              `t ++ G h`, `h::acc`,
                              `[]`, `h::acc`] BFT_CONS],
     FIRST_ASSUM MATCH_MP_TAC THEN RW_TAC set_ss [] THEN
       Cases_on `x IN REACH (EXCLUDE G (LIST_TO_SET seen)) h` THENL
       [POP_ASSUM MP_TAC THEN RW_TAC set_ss [REACH_LEM1] THEN
         FULL_SIMP_TAC set_ss [SPECIFICATION,REACH_LIST_def,LIST_TO_SET_THM]
         THEN METIS_TAC [],
        FULL_SIMP_TAC set_ss [SPECIFICATION, REACH_LIST_def,LIST_TO_SET_THM]
        THENL [METIS_TAC [], METIS_TAC [REACH_LEM2, EXCLUDE_LEM]]]]]);

(*---------------------------------------------------------------------------*)
(* x is reachable iff BFT finds it.                                          *)
(*---------------------------------------------------------------------------*)

Theorem BFT_REACH_THM:
  !G fringe.
    FINITE (Parents G)
      ==>
    !x. x IN REACH_LIST G fringe <=> MEM x (BFT G CONS [] fringe [])
Proof
 RW_TAC bool_ss [EQ_IMP_THM] THENL
 [MATCH_MP_TAC BFT_REACH_2,IMP_RES_TAC BFT_REACH_1] THEN
 FULL_SIMP_TAC set_ss [REACH_def,REACH_EXCLUDE,SPECIFICATION,REACH_LIST_def] THEN
 METIS_TAC[LIST_TO_SET_DEF]
QED

val _ = export_theory();
