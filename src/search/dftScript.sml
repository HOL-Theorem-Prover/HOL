(*---------------------------------------------------------------------------*)
(* Depth first traversal of directed graphs that can contain cycles.         *)
(*---------------------------------------------------------------------------*)

open HolKernel boolLib bossLib
     pred_setTheory pred_setLib relationTheory listTheory
     dirGraphTheory;

val set_ss = list_ss ++ PRED_SET_ss;
val dnf_ss = bool_ss ++ boolSimps.DNF_ss ++ rewrites [AND_IMP_INTRO];

val _ = numLib.temp_prefer_num();

val _ = new_theory "dft";

(*---------------------------------------------------------------------------*)
(* DFT :('a -> 'a list) ->   (* graph *)                                     *)
(*      ('a -> 'b -> 'b) ->  (* folding function *)                          *)
(*      'a list ->           (* nodes seen *)                                *)
(*      'a list ->           (* fringe to visit *)                           *)
(*      'b ->                (* accumulator *)                               *)
(*      'b                   (* final result *)                              *)
(*                                                                           *)
(* DFT checks that the given graph has finite Parents.  If the Parents set   *)
(* is finite then the graph has only finitely many edges (because G produces *)
(* a list of children, a node has only finitely many children) and DFT must  *)
(* terminate.                                                                *)
(*                                                                           *)
(* Termination proof. In the first recursive call, the to_visit list is      *)
(* shorter. In the second recursive call, the seen and to_visit argument can *)
(* both increase, but in different circumstances.  In this call, visit_now   *)
(* has not been seen.  If it is a parent in the graph, then adding it to     *)
(* seen decreases the number of unseen parents in the graph. If it is not a  *)
(* parent, then it has no children, and so the to_visit list shrinks.        *)
(*---------------------------------------------------------------------------*)

val Rel_def =   (* map arg. tuples into a pair of numbers for termination *)
 Define
   `Rel(G,f,seen,to_visit,acc) =
        (CARD(Parents G DIFF (LIST_TO_SET seen)), LENGTH to_visit)`;

val () = computeLib.auto_import_definitions := false

Definition def[induction=DFT_ind0]:
  DFT G f seen to_visit acc =
    if FINITE (Parents G)
      then case to_visit
           of [] => acc
           | visit_now :: visit_later =>
              if MEM visit_now seen
                then DFT G f seen visit_later acc
                else DFT G f (visit_now :: seen)
                             (G visit_now ++ visit_later)
                             (f visit_now acc)
      else ARB
Termination
 WF_REL_TAC `inv_image ($< LEX $<) Rel`
   THEN RW_TAC set_ss [Rel_def, DECIDE ``(0 < p - q) <=> q < p ``]
   THEN Cases_on `visit_now IN Parents G` THENL
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

val DFT_def = Q.store_thm
("DFT_def",
 `FINITE (Parents G) ==>
  (DFT G f seen [] acc = acc) /\
  (DFT G f seen (visit_now :: visit_later) acc =
    if MEM visit_now seen
       then DFT G f seen visit_later acc
       else DFT G f (visit_now :: seen)
                    (G visit_now ++ visit_later)
                    (f visit_now acc))`,
 RW_TAC std_ss [] THENL
 [RW_TAC list_ss [def],
  GEN_REWRITE_TAC LHS_CONV empty_rewrites [def] THEN RW_TAC list_ss [],
  RW_TAC list_ss [def],
  GEN_REWRITE_TAC LHS_CONV empty_rewrites [def] THEN RW_TAC list_ss []]);


(*---------------------------------------------------------------------------*)
(* Desired induction theorem for DFT.                                        *)
(*---------------------------------------------------------------------------*)

val DFT_ind = Q.store_thm
("DFT_ind",
 `!P.
    (!G f seen visit_now visit_later acc.
       P G f seen [] acc /\
       ((FINITE (Parents G) /\ ~MEM visit_now seen ==>
            P G f (visit_now :: seen)
                  (G visit_now ++ visit_later)
                  (f visit_now acc)) /\
        (FINITE (Parents G) /\ MEM visit_now seen ==>
            P G f seen visit_later acc)
         ==> P G f seen (visit_now :: visit_later) acc))
   ==>
   !v v1 v2 v3 v4. P v v1 v2 v3 v4`,
 NTAC 2 STRIP_TAC
 THEN HO_MATCH_MP_TAC DFT_ind0
 THEN REPEAT GEN_TAC THEN Cases_on `to_visit`
 THEN RW_TAC list_ss []);

(*---------------------------------------------------------------------------*)
(* Basic lemmas about DFT                                                    *)
(*---------------------------------------------------------------------------*)

val DFT_CONS = Q.store_thm
("DFT_CONS",
 `!G f seen to_visit acc a b.
    FINITE (Parents G) /\ (f = CONS) /\ (acc = APPEND a b)
      ==>
    (DFT G f seen to_visit acc = DFT G f seen to_visit a ++ b)`,
 recInduct DFT_ind
  THEN RW_TAC list_ss [DFT_def] THEN METIS_TAC [APPEND]);

val FOLDR_UNROLL = Q.prove
(`!f x b l. FOLDR f (f x b) l = FOLDR f b (l ++ [x])`,
 Induct_on `l` THEN RW_TAC list_ss []);

val DFT_FOLD = Q.store_thm
("DFT_FOLD",
 `!G f seen to_visit acc.
    FINITE (Parents G)
       ==>
   (DFT G f seen to_visit acc = FOLDR f acc (DFT G CONS seen to_visit []))`,
 recInduct DFT_ind THEN
 RW_TAC list_ss [DFT_def] THEN METIS_TAC [FOLDR_UNROLL,DFT_CONS,APPEND]);

val DFT_ALL_DISTINCT_LEM = Q.prove
(`!G f seen to_visit acc.
    FINITE (Parents G) /\ (f = CONS) /\
    ALL_DISTINCT acc /\ (!x. MEM x acc ==> MEM x seen)
      ==>
    ALL_DISTINCT (DFT G f seen to_visit acc)`,
 recInduct DFT_ind THEN RW_TAC list_ss [DFT_def] THEN METIS_TAC []);

val DFT_ALL_DISTINCT = Q.store_thm
("DFT_ALL_DISTINCT",
 `!G seen to_visit.
    FINITE (Parents G) ==> ALL_DISTINCT (DFT G CONS seen to_visit [])`,
 RW_TAC list_ss [DFT_ALL_DISTINCT_LEM]);

(*---------------------------------------------------------------------------*)
(* If DFT visits x, then x is reachable or is in the starting accumulator    *)
(*---------------------------------------------------------------------------*)

val DFT_REACH_1 = Q.store_thm
("DFT_REACH_1",
 `!G f seen to_visit acc.
    FINITE (Parents G) /\ (f = CONS) ==>
    !x. MEM x (DFT G f seen to_visit acc) ==>
      x IN (REACH_LIST G to_visit) \/ MEM x acc`,
 recInduct DFT_ind
   THEN RW_TAC set_ss [DFT_def, REACH_LIST_def, REACH_def, IN_DEF]
   THENL[METIS_TAC [], ALL_TAC]
   THEN POP_ASSUM MP_TAC THEN RW_TAC set_ss []
   THEN POP_ASSUM (MP_TAC o Q.SPEC `x`) THEN RW_TAC set_ss [] THENL
   [IMP_RES_TAC RTC_RULES THEN METIS_TAC[],
    METIS_TAC[], METIS_TAC[RTC_RULES], METIS_TAC[]]);

(*---------------------------------------------------------------------------*)
(* If x is reachable from to_visit on a path that does not include the nodes *)
(* in seen, then DFT visits x.                                               *)
(*---------------------------------------------------------------------------*)

val DFT_REACH_2 = Q.store_thm
("DFT_REACH_2",
 `!G f seen to_visit acc x.
    FINITE (Parents G) /\ (f = CONS) /\
    x IN (REACH_LIST (EXCLUDE G (LIST_TO_SET seen)) to_visit) /\
    ~MEM x seen
     ==>
      MEM x (DFT G f seen to_visit acc)`,
 recInduct DFT_ind THEN RW_TAC set_ss [DFT_def] THENL
 [(* Base Case *)
  FULL_SIMP_TAC list_ss [IN_DEF, EXCLUDE_def, REACH_LIST_def],
  (* The head of to_visit is in seen *)
  FULL_SIMP_TAC dnf_ss [SPECIFICATION, REACH_LIST_def]
  THEN RW_TAC list_ss [] THEN
  POP_ASSUM MP_TAC THEN RW_TAC list_ss [] THEN POP_ASSUM MATCH_MP_TAC THEN
  FULL_SIMP_TAC set_ss [SPECIFICATION, REACH_LIST_def] THENL
  [FULL_SIMP_TAC set_ss [REACH_EXCLUDE,Once RTC_CASES1,SPECIFICATION],ALL_TAC]
   THEN METIS_TAC [],
  (* The head of to_visit is not in seen *)
  POP_ASSUM MP_TAC THEN RW_TAC set_ss [] THEN
    POP_ASSUM (MP_TAC o Q.SPEC `x`) THEN RW_TAC list_ss [] THEN
    Cases_on `x = visit_now` THEN FULL_SIMP_TAC set_ss [] THEN
    RW_TAC set_ss [] THENL
    [RW_TAC list_ss [Q.SPECL [`G`, `CONS`, `h::seen`,
                              `G visit_now ++ visit_later`, `visit_now::acc`,
                              `[]`, `visit_now::acc`] DFT_CONS],
     FIRST_ASSUM MATCH_MP_TAC THEN RW_TAC set_ss [] THEN
       Cases_on `x IN REACH (EXCLUDE G (LIST_TO_SET seen)) visit_now` THENL
       [POP_ASSUM MP_TAC THEN RW_TAC set_ss [REACH_LEM1] THEN
         FULL_SIMP_TAC set_ss [SPECIFICATION,REACH_LIST_def,LIST_TO_SET_THM]
         THEN METIS_TAC [],
        FULL_SIMP_TAC set_ss [SPECIFICATION, REACH_LIST_def,LIST_TO_SET_THM]
        THENL [METIS_TAC [], METIS_TAC [REACH_LEM2, EXCLUDE_LEM]]]]]);

(*---------------------------------------------------------------------------*)
(* x is reachable iff DFT finds it.                                          *)
(*---------------------------------------------------------------------------*)

Theorem DFT_REACH_THM:
  !G to_visit.
    FINITE (Parents G)
      ==>
    !x. x IN REACH_LIST G to_visit <=> MEM x (DFT G CONS [] to_visit [])
Proof
 RW_TAC bool_ss [EQ_IMP_THM] THENL
 [MATCH_MP_TAC DFT_REACH_2,IMP_RES_TAC DFT_REACH_1] THEN
 FULL_SIMP_TAC set_ss [REACH_def,REACH_EXCLUDE,SPECIFICATION,REACH_LIST_def] THEN
 METIS_TAC[LIST_TO_SET_DEF]
QED

val _ = export_theory();
