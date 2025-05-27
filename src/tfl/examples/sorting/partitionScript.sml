(*---------------------------------------------------------------------------
          Theory of list partitions.
 ---------------------------------------------------------------------------*)
(* interactive use:
app load ["bossLib", "numLib"];
*)

open HolKernel Parse boolLib numLib bossLib listTheory;

val _ = new_theory "partition";

(*---------------------------------------------------------------------------
                 Partition a list by a predicate.
 ---------------------------------------------------------------------------*)

val part_def =
 Define
     `(part P [] l1 l2 = (l1,l2))
  /\  (part P (h::rst) l1 l2 =
          if P h then part P rst (h::l1) l2
                 else part P rst  l1  (h::l2))`;


(*---------------------------------------------------------------------------
     A packaged version of "part". Most theorems about "partition"
     will be instances of theorems about "part".
 ---------------------------------------------------------------------------*)

val partition_def =
 Define
     `partition P l = part P l [] []`;

(*---------------------------------------------------------------------------
              Theorems about "part"
 ---------------------------------------------------------------------------*)

val part_length = Q.store_thm
("part_length",
 `!P L l1 l2 p q.
    ((p,q) = part P L l1 l2)
    ==> (LENGTH L + LENGTH l1 + LENGTH l2 = LENGTH p + LENGTH q)`,
Induct_on `L`
  THEN RW_TAC list_ss [part_def]
  THEN RES_THEN MP_TAC
  THEN RW_TAC list_ss []);


val part_length_lem = Q.store_thm
("part_length_lem",
`!P L l1 l2 p q.
    ((p,q) = part P L l1 l2)
    ==>  LENGTH p <= LENGTH L + LENGTH l1 + LENGTH l2 /\
         LENGTH q <= LENGTH L + LENGTH l1 + LENGTH l2`,
RW_TAC bool_ss []
 THEN IMP_RES_THEN MP_TAC part_length
 THEN ARITH_TAC);


(*---------------------------------------------------------------------------
     Everything in the partitions occurs in the original list, and
     vice-versa. The goal has been generalized.
 ---------------------------------------------------------------------------*)

val MEM_APPEND_DISJ = Q.prove
(`!x l1 l2. MEM x (APPEND l1 l2) = MEM x l1 \/ MEM x l2`,
Induct_on `l1` THEN RW_TAC list_ss [APPEND,MEM] THEN PROVE_TAC[]);

val part_MEM = Q.store_thm
("part_MEM",
 `!P L a1 a2 l1 l2.
     ((a1,a2) = part P L l1 l2)
       ==>
      !x. MEM x (APPEND L (APPEND l1 l2)) = MEM x (APPEND a1 a2)`,
 Induct_on `L`
  THEN RW_TAC bool_ss [part_def]
  THENL [RW_TAC list_ss [], ALL_TAC, ALL_TAC]
  THEN RES_THEN MP_TAC THEN NTAC 2 (DISCH_THEN (K ALL_TAC))
  THEN DISCH_THEN (fn th => REWRITE_TAC [GSYM th])
  THEN RW_TAC list_ss [MEM,MEM_APPEND_DISJ] THEN PROVE_TAC[]);

(*---------------------------------------------------------------------------
       Each element in the positive and negative partitions has
       the desired property. The simplifier loops on some of the
       subgoals here, so we have to take round-about measures.
 ---------------------------------------------------------------------------*)

val parts_have_prop = Q.store_thm
("parts_have_prop",
 `!P L A B l1 l2.
   ((A,B) = part P L l1 l2) /\
   (!x. MEM x l1 ==> P x) /\ (!x. MEM x l2 ==> ~P x)
    ==>
      (!z. MEM z A ==>  P z) /\ (!z. MEM z B ==> ~P z)`,
Induct_on `L`
 THEN REWRITE_TAC [part_def,pairTheory.CLOSED_PAIR_EQ] THENL
 [PROVE_TAC[],
  POP_ASSUM (fn th => REPEAT GEN_TAC THEN
     COND_CASES_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th)
   THENL [MAP_EVERY Q.EXISTS_TAC [`h::l1`, `l2`],
          MAP_EVERY Q.EXISTS_TAC [`l1`, `h::l2`]]
  THEN RW_TAC list_ss [MEM] THEN RW_TAC bool_ss []]);

val _ = export_theory();
