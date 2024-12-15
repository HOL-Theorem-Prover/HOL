(*---------------------------------------------------------------------------*)
(* Depth first traversal of directed graphs that can contain cycles.         *)
(*---------------------------------------------------------------------------*)

open HolKernel boolLib bossLib
     pred_setTheory pred_setLib relationTheory listTheory;

val set_ss = list_ss ++ PRED_SET_ss;

val _ = new_theory "dirGraph";

(*---------------------------------------------------------------------------*)
(* A graph G is a function of type 'a -> 'a list.                            *)
(* A node of G is a parent iff it has children.                              *)
(*---------------------------------------------------------------------------*)

val Parents_def =
 Define
   `Parents G = {x | ~(G x = [])}`;

(*---------------------------------------------------------------------------*)
(* Definition of reachability in a directed graph represented as a function  *)
(* from nodes to a finite number of children, i.e., of type 'a -> 'a list    *)
(*---------------------------------------------------------------------------*)

val REACH_def =
 Define
   `REACH G = RTC (\x y. MEM y (G x))`;

val REACH_LIST_def =
 Define
   `REACH_LIST G nodes y = ?x. MEM x nodes /\ y IN REACH G x`;

(*---------------------------------------------------------------------------*)
(* Removing a set of nodes ex from G.                                        *)
(*---------------------------------------------------------------------------*)

val EXCLUDE_def =
 Define
   `EXCLUDE G ex node = if node IN ex then [] else G node`;

(*---------------------------------------------------------------------------*)
(* Lemmas about reachability and restricted graphs.                          *)
(*---------------------------------------------------------------------------*)

val EXCLUDE_LEM = Q.store_thm
("EXCLUDE_LEM",
 `!G x l. EXCLUDE G (x INSERT l) = EXCLUDE (EXCLUDE G l) {x}`,
 RW_TAC set_ss [FUN_EQ_THM,EXTENSION, EXCLUDE_def, IN_INSERT, NOT_IN_EMPTY]
  THEN METIS_TAC[]);

val REACH_EXCLUDE = Q.store_thm
("REACH_EXCLUDE",
`!G x. REACH (EXCLUDE G x) = RTC (\x' y. ~(x' IN x) /\ MEM y (G x'))`,
 RW_TAC set_ss [REACH_def, EXCLUDE_def] THEN AP_TERM_TAC
  THEN RW_TAC set_ss [FUN_EQ_THM]
  THEN RW_TAC set_ss []);

(*---------------------------------------------------------------------------*)
(* A node is reachable from p iff it is reachable from a child of p on a     *)
(* path not containing p.                                                    *)
(*---------------------------------------------------------------------------*)

val REACH_LEM1 = Q.store_thm
("REACH_LEM1",
`!p G seen.
    ~(p IN seen) ==>
     (REACH (EXCLUDE G seen) p =
      p INSERT (REACH_LIST (EXCLUDE G (p INSERT seen)) (G p)))`,
 RW_TAC set_ss [EXTENSION,SPECIFICATION,REACH_EXCLUDE,REACH_LIST_def]
  THEN Cases_on `p = x`
  THEN RW_TAC list_ss [RTC_RULES] THEN EQ_TAC THEN RW_TAC bool_ss [] THENL
 [Q.PAT_ASSUM `$~a` MP_TAC THEN POP_ASSUM MP_TAC
   THEN Q.SPEC_TAC (`x`,`q`) THEN Q.ID_SPEC_TAC `p`
   THEN HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN RW_TAC bool_ss []
   THEN Cases_on `p' = x'` THEN FULL_SIMP_TAC bool_ss [] THENL
   [METIS_TAC [RTC_RULES],
    Q.EXISTS_TAC `x''` THEN RW_TAC bool_ss [Once RTC_CASES2] THEN METIS_TAC[]],
  `RTC (\x' y. ~seen x' /\ set (G x') y) x' x`
    by (POP_ASSUM MP_TAC THEN MATCH_MP_TAC RTC_MONOTONE THEN METIS_TAC[])
    THEN RW_TAC bool_ss [Once RTC_CASES1] THEN METIS_TAC []]);

(*---------------------------------------------------------------------------*)
(* If y is reachable from x, but not z, then y is reachable from x on a path *)
(* that does not include z.                                                  *)
(*---------------------------------------------------------------------------*)

val REACH_LEM2 = Q.store_thm
("REACH_LEM2",
 `!G x y. REACH G x y ==> !z. ~REACH G z y ==> REACH (EXCLUDE G {z}) x y`,
 STRIP_TAC THEN REWRITE_TAC [REACH_EXCLUDE, REACH_def, IN_SING] THEN
 HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN RW_TAC set_ss [RTC_RULES] THEN
 POP_ASSUM MP_TAC THEN RW_TAC set_ss [Once RTC_CASES2] THEN
 POP_ASSUM (MP_TAC o Q.SPEC `x'`) THEN RW_TAC set_ss [] THEN
 RW_TAC set_ss [Once RTC_CASES2] THEN METIS_TAC [RTC_RULES]);

val _ = export_theory();
