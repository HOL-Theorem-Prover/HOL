(*---------------------------------------------------------------------------*
 *  General specification of sorting and correctness of quicksort            *
 *---------------------------------------------------------------------------*)

structure sortingScript =
struct

(* interactive use:
app load ["permTheory","bossLib"];
*)

open HolKernel Parse boolLib bossLib 
     combinTheory pairTheory relationTheory listTheory;


val _ = new_theory "sorting";


val _ = Defn.def_suffix := "_DEF";
val _ = Defn.ind_suffix := "_IND";

(*---------------------------------------------------------------------------*
 * What's a permutation? This definition uses universal quantification to    *
 * define it. There are other ways, which could be compared to this, e.g.    *
 * as an inductive definition, or as a particular kind of function.          *
 *---------------------------------------------------------------------------*)

val PERM_DEF = Define `PERM L1 L2 = !x. FILTER ($= x) L1 = FILTER ($= x) L2`;


val PERM_REFL = Q.store_thm
("PERM_REFL",
    `!L. PERM L L`,
    PROVE_TAC[PERM_DEF]);


val PERM_INTRO = Q.store_thm
("PERM_INTRO",
    `!x y. (x=y) ==> PERM x y`,
    PROVE_TAC[PERM_REFL]);


val PERM_TRANS = Q.store_thm
("PERM_TRANS",
  `transitive PERM`,
 RW_TAC list_ss [relationTheory.transitive_def] 
  THEN PROVE_TAC[PERM_DEF]);


val PERM_TRANS1 = save_thm
("PERM_TRANS1",
 REWRITE_RULE [relationTheory.transitive_def] PERM_TRANS);


val PERM_SYM = Q.store_thm
("PERM_SYM",
  `!l1 l2. PERM l1 l2 = PERM l2 l1`,
PROVE_TAC [PERM_DEF]);

val PERM_CONG = Q.store_thm
("PERM_CONG",
 `!(L1:'a list) L2 L3 L4. 
     PERM L1 L3 /\ 
     PERM L2 L4
     ==> PERM (APPEND L1 L2) (APPEND L3 L4)`,
 PROVE_TAC [PERM_DEF,FILTER_APPEND_DISTRIB]);

val CONS_APPEND = PROVE [APPEND] (Term`!L h. h::L = APPEND [h] L`);

val PERM_MONO = Q.store_thm
("PERM_MONO",
 `!l1 l2 x. PERM l1 l2 ==> PERM (x::l1) (x::l2)`,
 PROVE_TAC [CONS_APPEND,PERM_CONG, PERM_REFL]);


val PERM_CONS_IFF = 
let val lem = Q.prove
     (`PERM (x::l1) (x::l2) ==> PERM l1 l2`,
      RW_TAC list_ss [PERM_DEF,FILTER]
        THEN POP_ASSUM (MP_TAC o Q.SPEC`x'`)
        THEN RW_TAC list_ss [])
in 
  save_thm ("PERM_CONS_IFF",
            GEN_ALL(IMP_ANTISYM_RULE lem (SPEC_ALL PERM_MONO)))
end;

val PERM_NIL = Q.store_thm
("PERM_NIL",
 `!L. (PERM L [] = (L=[])) /\ 
      (PERM [] L = (L=[]))`,
Cases THEN RW_TAC list_ss [PERM_DEF,FILTER]
 THEN Q.EXISTS_TAC `h`
 THEN RW_TAC list_ss []);


val lem = Q.prove(
 `!h l1 l2. APPEND (FILTER ($=h) l1) (h::l2)
            = h::APPEND (FILTER ($=h) l1) l2`,
Induct_on `l1` 
   THEN RW_TAC list_ss [FILTER] 
   THEN PROVE_TAC[]);


val PERM_APPEND = Q.store_thm
("PERM_APPEND",
 `!l1 l2. PERM (APPEND l1 l2) (APPEND l2 l1)`,
RW_TAC list_ss [PERM_DEF,FILTER_APPEND_DISTRIB]
  THEN Induct_on `l1` 
  THEN RW_TAC list_ss [FILTER,lem]
  THEN PROVE_TAC[]);;


val CONS_PERM = Q.store_thm
("CONS_PERM",
 `!x L M N. PERM L (APPEND M N) 
            ==> 
           PERM (x::L) (APPEND M (x::N))`,
RW_TAC bool_ss []
 THEN MATCH_MP_TAC PERM_TRANS1
 THEN PROVE_TAC [PERM_MONO, PERM_APPEND, APPEND, PERM_TRANS1]);


val APPEND_PERM_SYM = Q.store_thm
("APPEND_PERM_SYM",
 `!A B C. PERM (APPEND A B) C ==> PERM (APPEND B A) C`,
PROVE_TAC [PERM_TRANS1, PERM_APPEND]);

val PERM_SPLIT = Q.store_thm
("PERM_SPLIT",
 `!P l. PERM l (APPEND (FILTER P l) (FILTER ($~ o P) l))`,
RW_TAC bool_ss [o_DEF]
 THEN Induct_on `l`
 THEN RW_TAC list_ss [FILTER,PERM_REFL] 
 THEN PROVE_TAC [APPEND,PERM_MONO,CONS_PERM]);


(*---------------------------------------------------------------------------
    Directly performs one "sorting step" between 2 non-empty lists that 
    are permutations of each other.
 *---------------------------------------------------------------------------*)

val PERM_SORT_STEP = Q.store_thm
("PERM_SORT_STEP",
 `!l h t. PERM (h::t) l ==> ?rst. h::rst = FILTER ($=h) l`,
 RW_TAC list_ss [PERM_DEF,FILTER] 
   THEN POP_ASSUM (MP_TAC o Q.SPEC`h`)
   THEN RW_TAC bool_ss []
   THEN PROVE_TAC[]);

val LENGTH_APPEND_FILTER = Q.prove
(`!L. LENGTH L = LENGTH (APPEND (FILTER P L) (FILTER ($~ o P) L))`,
Induct 
 THEN RW_TAC list_ss [FILTER, o_DEF] 
 THEN PROVE_TAC []);

val PERM_STEP = Q.prove
(`!l h t. PERM (h::t) l 
            ==> 
          ?u. PERM l (h::u) /\ (LENGTH l = LENGTH (h::u))`,
RW_TAC bool_ss []
  THEN IMP_RES_TAC PERM_SORT_STEP
  THEN Q.EXISTS_TAC `APPEND rst (FILTER ($~ o $= h) l)`
  THEN PROVE_TAC [APPEND, LENGTH_APPEND_FILTER,PERM_SPLIT]);


val PERM_LENGTH = Q.store_thm("PERM_LENGTH",
`!l1 l2. PERM l1 l2 ==> (LENGTH l1 = LENGTH l2)`,
Induct 
  THEN RW_TAC list_ss [PERM_NIL]
  THEN IMP_RES_TAC PERM_STEP
  THEN `PERM l1 u` by PROVE_TAC [PERM_TRANS1,PERM_CONS_IFF]
  THEN RW_TAC list_ss []);


(*---------------------------------------------------------------------------*
 * The idea of sortedness requires a "permutation" relation for lists, and   *
 * a "chain" predicate that holds just when the relation R holds between     *
 * all adjacent elements of the list.                                        *
 *---------------------------------------------------------------------------*)

val SORTED_DEF = Define `(SORTED R [] = T) /\ (SORTED R [x] = T) /\
 (SORTED R (x::y::rst) = R x y /\ SORTED R (y::rst))`;


val SORTS_DEF = 
 Define
    `SORTS f R = !l. PERM l (f R l) /\ SORTED R (f R l)`;


(*---------------------------------------------------------------------------*
 *    When consing onto a sorted list yields a sorted list                   *
 *---------------------------------------------------------------------------*)

val SORTED_EQ = Q.store_thm
("SORTED_EQ",
 `!R L x. transitive R ==> (SORTED R (x::L) = SORTED R L /\ !y. MEM y L ==> R x y)`,
Induct_on `L`
 THEN RW_TAC list_ss [SORTED_DEF,MEM] 
 THEN PROVE_TAC [relationTheory.transitive_def]);


(*---------------------------------------------------------------------------*
 *       When appending sorted lists gives a sorted list.                    *
 *---------------------------------------------------------------------------*)

val SORTED_APPEND = Q.store_thm("SORTED_APPEND",
`!R L1 L2. 
     transitive R 
 /\  SORTED R L1
 /\  SORTED R L2
 /\ (!x y. MEM x L1 /\ MEM y L2 ==> R x y)
  ==> 
    SORTED R (APPEND L1 L2)`,
Induct_on `L1`
 THEN RW_TAC list_ss [MEM] 
 THEN `SORTED R L1 /\ !y. MEM y L1 ==> R h y` by PROVE_TAC [SORTED_EQ]
 THEN RW_TAC bool_ss [SORTED_EQ] 
 THEN `MEM y L1 \/ MEM y L2` by PROVE_TAC [MEM_APPEND]
 THEN PROVE_TAC []);


(*---------------------------------------------------------------------------
                 Partition a list by a predicate.
 ---------------------------------------------------------------------------*)

val PART_DEF = 
 Define 
     `(PART P [] l1 l2 = (l1,l2))
  /\  (PART P (h::rst) l1 l2 = 
          if P h then PART P rst (h::l1) l2
                 else PART P rst  l1  (h::l2))`;


(*---------------------------------------------------------------------------
              Theorems about "PART"
 ---------------------------------------------------------------------------*)

val PART_LENGTH = Q.store_thm
("PART_LENGTH",
 `!P L l1 l2 p q.
    ((p,q) = PART P L l1 l2)
    ==> (LENGTH L + LENGTH l1 + LENGTH l2 = LENGTH p + LENGTH q)`,
Induct_on `L` 
  THEN RW_TAC list_ss [PART_DEF]
  THEN RES_THEN MP_TAC 
  THEN RW_TAC list_ss []);


val PART_LENGTH_LEM = Q.store_thm
("PART_LENGTH_LEM",
`!P L l1 l2 p q. 
    ((p,q) = PART P L l1 l2)
    ==>  LENGTH p <= LENGTH L + LENGTH l1 + LENGTH l2 /\
         LENGTH q <= LENGTH L + LENGTH l1 + LENGTH l2`,
RW_TAC bool_ss []
 THEN IMP_RES_THEN MP_TAC PART_LENGTH
 THEN RW_TAC list_ss []);


(*---------------------------------------------------------------------------
     Everything in the partitions occurs in the original list, and 
     vice-versa. The goal has been generalized. 
 ---------------------------------------------------------------------------*)

val PART_MEM = Q.store_thm
("PART_MEM",
 `!P L a1 a2 l1 l2. 
     ((a1,a2) = PART P L l1 l2) 
       ==> 
      !x. MEM x (APPEND L (APPEND l1 l2)) = MEM x (APPEND a1 a2)`,
 Induct_on `L` 
  THEN RW_TAC bool_ss [PART_DEF]
  THENL [RW_TAC list_ss [], ALL_TAC, ALL_TAC]
  THEN RES_THEN MP_TAC THEN NTAC 2 (DISCH_THEN (K ALL_TAC))
  THEN DISCH_THEN (fn th => REWRITE_TAC [GSYM th])
  THEN RW_TAC list_ss [MEM,MEM_APPEND] THEN PROVE_TAC[]);

(*---------------------------------------------------------------------------
       Each element in the positive and negative partitions has 
       the desired property. The simplifier loops on some of the 
       subgoals here, so we have to take round-about measures.
 ---------------------------------------------------------------------------*)

val PARTS_HAVE_PROP = Q.store_thm
("PARTs_HAVE_PROP",
 `!P L A B l1 l2. 
   ((A,B) = PART P L l1 l2) /\
   (!x. MEM x l1 ==> P x) /\ (!x. MEM x l2 ==> ~P x)
    ==> 
      (!z. MEM z A ==>  P z) /\ (!z. MEM z B ==> ~P z)`,
Induct_on `L`
 THEN REWRITE_TAC [PART_DEF,CLOSED_PAIR_EQ] THENL
 [PROVE_TAC[],
  POP_ASSUM (fn th => REPEAT GEN_TAC THEN 
     COND_CASES_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th)
   THENL [MAP_EVERY Q.EXISTS_TAC [`h::l1`, `l2`],
          MAP_EVERY Q.EXISTS_TAC [`l1`, `h::l2`]]
  THEN RW_TAC list_ss [MEM] THEN RW_TAC bool_ss []]);


(*---------------------------------------------------------------------------*)
(* Appending the two partitions of the original list is a permutation of the *)
(* original list.                                                            *)
(*---------------------------------------------------------------------------*)

val PART_PERM = Q.prove
(`!P L a1 a2 l1 l2.
   ((a1,a2) = PART P L l1 l2)
      ==>
   PERM (APPEND L (APPEND l1 l2)) (APPEND a1 a2)`,
Induct_on `L`
  THEN RW_TAC list_ss [PART_DEF, PERM_REFL]
  THEN RES_TAC THEN MATCH_MP_TAC PERM_TRANS1 THENL
  [Q.EXISTS_TAC `APPEND L (APPEND (h::l1) l2)`,
   Q.EXISTS_TAC `APPEND L (APPEND l1 (h::l2))`]
  THEN PROVE_TAC [APPEND,APPEND_ASSOC,CONS_PERM,PERM_REFL]);

(*---------------------------------------------------------------------------
     A packaged version of PART. Most theorems about PARTITION 
     will be instances of theorems about PART. 
 ---------------------------------------------------------------------------*)

val PARTITION_DEF = Define`PARTITION P l = PART P l [] []`;


(*---------------------------------------------------------------------------*
 *      Quicksort                                                            *
 *---------------------------------------------------------------------------*)

val QSORT_defn =
 Hol_defn "QSORT"
    `(QSORT ord [] = []) /\
     (QSORT ord (h::t) =
           let (l1,l2) = PARTITION (\y. ord y h) t
           in
           APPEND (QSORT ord l1)
               (h::QSORT ord l2))`;


(*---------------------------------------------------------------------------
 * Termination of QSORT
 *---------------------------------------------------------------------------*)

val (QSORT_DEF,QSORT_IND) = Defn.tprove
 (QSORT_defn,
  WF_REL_TAC `measure (LENGTH o SND)`
     THEN RW_TAC list_ss [o_DEF,PARTITION_DEF]
     THEN IMP_RES_THEN MP_TAC PART_LENGTH_LEM
     THEN RW_TAC list_ss []);

val _ = save_thm("QSORT_DEF",QSORT_DEF);
val _ = save_thm("QSORT_IND",QSORT_IND);

(*---------------------------------------------------------------------------*
 *           Properties of QSORT                                            *
 *---------------------------------------------------------------------------*)

val QSORT_MEM_STABLE = Q.store_thm
("QSORT_MEM",
 `!R L x. MEM x (QSORT R L) = MEM x L`,
recInduct QSORT_IND
 THEN RW_TAC bool_ss [QSORT_DEF,PARTITION_DEF]
 THEN RW_TAC list_ss []
 THEN Q.PAT_ASSUM `x = y` (MP_TAC o MATCH_MP PART_MEM o SYM)
 THEN RW_TAC list_ss [] THEN PROVE_TAC []);

(*---------------------------------------------------------------------------*)
(* The result list is a permutation of the input list.                       *)
(*---------------------------------------------------------------------------*)


val QSORT_PERM = Q.store_thm
("QSORT_PERM",
 `!R L. PERM L (QSORT R L)`,
 recInduct QSORT_IND
  THEN RW_TAC bool_ss [QSORT_DEF,PERM_REFL,PARTITION_DEF]
  THEN MATCH_MP_TAC CONS_PERM
  THEN MATCH_MP_TAC PERM_TRANS1
  THEN Q.EXISTS_TAC`APPEND l1 l2`
  THEN RW_TAC std_ss [] THENL
  [PROVE_TAC [APPEND,APPEND_NIL,PART_PERM],
   `PERM l1 (QSORT ord l1)` by RES_TAC THEN
   `PERM l2 (QSORT ord l2)` by RES_TAC THEN PROVE_TAC [PERM_CONG]]);


(*---------------------------------------------------------------------------
 * The result list is sorted.
 *---------------------------------------------------------------------------*)

val QSORT_SORTED =
Q.store_thm
("QSORT_SORTED",
`!R L. transitive R /\ total R ==> SORTED R (QSORT R L)`,
 recInduct QSORT_IND
  THEN RW_TAC bool_ss [QSORT_DEF, SORTED_DEF, PARTITION_DEF]
  THEN MATCH_MP_TAC SORTED_APPEND
  THEN POP_ASSUM (ASSUME_TAC o SYM)
  THEN IMP_RES_THEN (fn th => ASM_REWRITE_TAC [th]) SORTED_EQ
  THEN RW_TAC list_ss [MEM_FILTER,MEM,QSORT_MEM_STABLE]
  THEN ((RES_TAC THEN NO_TAC) ORELSE ALL_TAC)
  THEN Q.PAT_ASSUM `x = y` (MP_TAC o MATCH_MP
        (REWRITE_RULE[PROVE [] (Term `x/\y/\z ==> w = x ==> y/\z ==> w`)]
            PARTS_HAVE_PROP))
  THEN RW_TAC std_ss [MEM]
  THEN PROVE_TAC [transitive_def,total_def]);


(*---------------------------------------------------------------------------
 * Bring everything together.
 *---------------------------------------------------------------------------*)

val QSORT_SORTS = Q.store_thm
("QSORT_SORTS",
 `!R. transitive R /\ total R ==> SORTS QSORT R`,
  PROVE_TAC [SORTS_DEF, QSORT_PERM, QSORT_SORTED]);


val _ = export_theory();

val _ = 
 let open EmitML
 in exportML("sorting",
  [OPEN ["list"],
   DEFN PART_DEF, 
   DEFN PARTITION_DEF,
   DEFN QSORT_DEF,
   DEFN SORTED_DEF])
 end;

end;
