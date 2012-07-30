(*---------------------------------------------------------------------------*
 *  General specification of sorting and correctness of quicksort            *
 *---------------------------------------------------------------------------*)

structure sortingScript =
struct

open HolKernel Parse boolLib bossLib;
open combinTheory pairTheory relationTheory listTheory
     markerLib metisLib BasicProvers;

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
val _ = export_rewrites ["PERM_REFL"]


val PERM_INTRO = Q.store_thm
("PERM_INTRO",
    `!x y. (x=y) ==> PERM x y`,
    PROVE_TAC[PERM_REFL]);


val PERM_transitive = Q.store_thm
("PERM_transitive",
  `transitive PERM`,
 RW_TAC list_ss [relationTheory.transitive_def]
  THEN PROVE_TAC[PERM_DEF]);

val PERM_TRANS = Q.store_thm
("PERM_TRANS",
 `!x y z. PERM x y /\ PERM y z ==> PERM x z`,
 METIS_TAC [relationTheory.transitive_def, PERM_transitive])

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

val _ = export_rewrites ["PERM_CONS_IFF"]

val PERM_NIL = Q.store_thm
("PERM_NIL",
 `!L. (PERM L [] = (L=[])) /\
      (PERM [] L = (L=[]))`,
Cases THEN RW_TAC list_ss [PERM_DEF,FILTER]
 THEN Q.EXISTS_TAC `h`
 THEN RW_TAC list_ss []);

val _ = export_rewrites ["PERM_NIL"]

val PERM_SING = Q.store_thm
("PERM_SING",
 `(PERM L [x] = (L = [x])) /\ (PERM [x] L = (L = [x]))`,
 Q_TAC SUFF_TAC `PERM L [x] = (L = [x])`
       THEN1 METIS_TAC [PERM_SYM] THEN
 Cases_on `L` THEN SIMP_TAC (srw_ss()) [PERM_DEF, EQ_IMP_THM] THEN
 Q_TAC SUFF_TAC
       `(!y. (if y = h then h :: FILTER ($= h) t else FILTER ($= y) t) =
             (if y = x then [x] else [])) ==>
        (h = x) /\ (t = [])`
       THEN1 METIS_TAC [] THEN
 STRIP_TAC THEN
 `h = x` by (POP_ASSUM (Q.SPEC_THEN `h` MP_TAC) THEN SRW_TAC [][]) THEN
 SRW_TAC [][] THEN
 `!y. FILTER ($= y) t = []` by METIS_TAC [CONS_11] THEN
 Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 METIS_TAC [NOT_CONS_NIL]);
val _ = export_rewrites ["PERM_SING"]

val MEM_FILTER_EQ = Q.prove
(`!l x. MEM x l = ~(FILTER ($= x) l = [])`,
 Induct THEN SRW_TAC [][]);

val MEM_APPEND_SPLIT = Q.prove
(`!L x. MEM x L ==> ?M N. L = M ++ x::N`,
 Induct THEN SRW_TAC [][] THENL [
   Q.EXISTS_TAC `[]` THEN SRW_TAC [][],
   `?M N. L = M ++ x::N` by METIS_TAC [] THEN
   Q.EXISTS_TAC `h::M` THEN SRW_TAC [][]
 ]);

val FILTER_EQ_CONS_APPEND = Q.prove
(`!M N x. FILTER ($= x) M ++ x::N = x::FILTER ($= x) M ++ N`,
 Induct THEN SRW_TAC [][])

val PERM_CONS_EQ_APPEND = Q.store_thm
("PERM_CONS_EQ_APPEND",
 `!L h. PERM (h::t) L = ?M N. (L = M ++ h::N) /\ PERM t (M ++ N)`,
 SRW_TAC [][PERM_DEF, FILTER_APPEND_DISTRIB, EQ_IMP_THM] THENL [
   `MEM h L` by METIS_TAC [NOT_CONS_NIL, MEM_FILTER_EQ] THEN
   `?M N. L = M ++ h::N` by METIS_TAC [MEM_APPEND_SPLIT] THEN
   MAP_EVERY Q.EXISTS_TAC [`M`, `N`] THEN
   SRW_TAC [][] THEN Cases_on `x = h` THEN
   FIRST_X_ASSUM (Q.SPEC_THEN `x` MP_TAC) THEN
   SRW_TAC [][FILTER_APPEND_DISTRIB, FILTER_EQ_CONS_APPEND],
   SRW_TAC [][FILTER_APPEND_DISTRIB, FILTER_EQ_CONS_APPEND]
 ]);

val PERM_APPEND = Q.store_thm
("PERM_APPEND",
 `!l1 l2. PERM (APPEND l1 l2) (APPEND l2 l1)`,
 Induct THEN SRW_TAC [][PERM_CONS_EQ_APPEND] THEN METIS_TAC [])

val CONS_PERM = Q.store_thm
("CONS_PERM",
 `!x L M N. PERM L (APPEND M N)
            ==>
           PERM (x::L) (APPEND M (x::N))`,
METIS_TAC [PERM_CONS_EQ_APPEND]);


val APPEND_PERM_SYM = Q.store_thm
("APPEND_PERM_SYM",
 `!A B C. PERM (APPEND A B) C ==> PERM (APPEND B A) C`,
PROVE_TAC [PERM_TRANS, PERM_APPEND]);

val PERM_SPLIT = Q.store_thm
("PERM_SPLIT",
 `!P l. PERM l (APPEND (FILTER P l) (FILTER ($~ o P) l))`,
RW_TAC bool_ss [o_DEF]
 THEN Induct_on `l`
 THEN RW_TAC list_ss [FILTER,PERM_REFL]
 THEN PROVE_TAC [APPEND,PERM_MONO,CONS_PERM]);

(* ----------------------------------------------------------------------
    Inductive characterisation of PERM
   ---------------------------------------------------------------------- *)

(* things become slightly awkward because I avoid actually defining an
   inductive version of the permutation constant.  Instead, I do a bunch
   of proofs subject to an assumption "defining" perm to be the
   appropriate RHS; an alernative would be to define the constant, work
   with it, and then to delete it, so that it didn't get exported. *)

(* the definition assumption is 'backwards' so that it will be OK as an
   assumption and not cause perm to get rewritten out *)
val perm_t =
  ``permdef :- !l1 l2:'a list.
                  perm l1 l2 =
                    (!P. P [] [] /\
                         (!x l1 l2. P l1 l2 ==> P (x::l1) (x::l2)) /\
                         (!x y l1 l2. P l1 l2 ==> P (x::y::l1) (y::x::l2)) /\
                         (!l1 l2 l3. P l1 l2 /\ P l2 l3 ==> P l1 l3) ==>
                         P l1 l2)``

(* perm's induction principle *)
val _ = print "Proving perm induction principle\n"
val perm_ind = prove(
  ``^perm_t ==> !P. P [] [] /\
                    (!x l1 l2. P l1 l2 ==> P (x::l1) (x::l2)) /\
                    (!x y l1 l2. P l1 l2 ==> P (x::y::l1) (y::x::l2)) /\
                    (!l1 l2 l3. P l1 l2 /\ P l2 l3 ==> P l1 l3) ==>
                    !l1 l2. perm l1 l2 ==> P l1 l2``,
  STRIP_TAC THEN LABEL_X_ASSUM "permdef" (REWRITE_TAC o C cons nil) THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []);
val perm_ind = UNDISCH perm_ind

val _ = print "Proving perm rules\n"
val perm_rules = prove(
  ``^perm_t ==> perm [] [] /\
                (!x l1 l2. perm l1 l2 ==> perm (x::l1) (x::l2)) /\
                (!x y l1 l2. perm l1 l2 ==> perm (x::y::l1) (y::x::l2)) /\
                (!l1 l2 l3. perm l1 l2 /\ perm l2 l3 ==> perm l1 l3)``,
  STRIP_TAC THEN LABEL_X_ASSUM "permdef" (REWRITE_TAC o C cons nil) THEN
  REPEAT STRIP_TAC THEN
  REPEAT
    (FIRST_X_ASSUM (MP_TAC o SPEC ``P : 'a list -> 'a list -> bool``)) THEN
  ASM_REWRITE_TAC [] THEN METIS_TAC [])

val perm_rules = UNDISCH perm_rules;

val _ = print "Proving perm symmetric, reflexive & transitive\n"

val perm_sym = prove(
  ``^perm_t ==> (perm l1 l2 = perm l2 l1)``,
  STRIP_TAC THEN
  Q_TAC SUFF_TAC
        `!l1 l2. perm l1 l2 ==> perm l2 l1`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC perm_ind THEN
  SRW_TAC [][perm_rules] THEN METIS_TAC [perm_rules]);
val perm_sym = UNDISCH perm_sym

val perm_refl = prove(
  ``^perm_t ==> !l. perm l l``,
  STRIP_TAC THEN Induct THEN SRW_TAC [][perm_rules]);
val perm_refl = UNDISCH perm_refl

val perm_trans = last (CONJUNCTS perm_rules)

val _ = print "Proving perm ==> PERM\n"

val perm_PERM = prove(
  ``^perm_t ==> !l1 l2. perm l1 l2 ==> PERM l1 l2``,
  STRIP_TAC THEN HO_MATCH_MP_TAC perm_ind THEN SRW_TAC [][] THENL [
    SRW_TAC [][PERM_CONS_EQ_APPEND] THEN
    MAP_EVERY Q.EXISTS_TAC [`[y]`, `l2`] THEN SRW_TAC [][] THEN
    MAP_EVERY Q.EXISTS_TAC [`[]`, `l2`] THEN SRW_TAC [][],
    METIS_TAC [PERM_TRANS]
  ]);
val perm_PERM = UNDISCH perm_PERM

val _ = print "Proving perm has primitive recursive characterisation\n"

val perm_cons_append = prove(
  ``^perm_t ==> !l1 l2. perm l1 l2 ==>
                        !M N. (l2 = M ++ N) ==>
                              !h. perm (h::l1) (M ++ [h] ++ N)``,
  STRIP_TAC THEN HO_MATCH_MP_TAC perm_ind THEN SRW_TAC [][] THENL [
    SRW_TAC [][perm_rules],
    Cases_on `M` THEN SRW_TAC [][] THENL [
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      METIS_TAC [perm_rules, APPEND],
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      METIS_TAC [perm_rules, perm_refl]
    ],
    `(M = []) \/ (?m1 ms. M = m1::ms)` by (Cases_on `M` THEN SRW_TAC [][]) THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THENL [
      METIS_TAC [perm_rules, APPEND, perm_refl],
      `(ms = []) \/ (?m2 mss. ms = m2::mss)`
          by (Cases_on `ms` THEN SRW_TAC [][]) THEN
      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      METIS_TAC [perm_rules, APPEND, perm_refl]
    ],
    METIS_TAC [perm_trans, APPEND]
  ])
val perm_cons_append =
    SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [] (UNDISCH perm_cons_append)

val _ = print "Proving PERM ==> perm\n"

val PERM_perm = prove(
  ``^perm_t ==> !l1 l2. PERM l1 l2 ==> perm l1 l2``,
  STRIP_TAC THEN Induct THEN SRW_TAC [][perm_rules, PERM_CONS_EQ_APPEND] THEN
  METIS_TAC [perm_cons_append])
val PERM_perm = UNDISCH PERM_perm

val perm_elim = GEN_ALL
                  (IMP_ANTISYM_RULE (SPEC_ALL perm_PERM) (SPEC_ALL PERM_perm))
fun remove_eq_asm th = let
  val th0 =
      CONV_RULE (LAND_CONV
                   (SIMP_CONV (bool_ss ++ boolSimps.ETA_ss)
                              [GSYM FUN_EQ_THM, markerTheory.label_def]))
                (DISCH_ALL (REWRITE_RULE [perm_elim] th))
in
  CONV_RULE Unwind.UNWIND_FORALL_CONV
            (GEN ``perm : 'a list -> 'a list -> bool`` th0)
end

val PERM_IND = save_thm("PERM_IND", remove_eq_asm perm_ind)

val PERM_SWAP_AT_FRONT = store_thm(
  "PERM_SWAP_AT_FRONT",
  ``PERM (x::y::l1) (y::x::l2) = PERM l1 l2``,
  METIS_TAC [remove_eq_asm (List.nth(CONJUNCTS perm_rules, 2)),
             PERM_REFL, PERM_TRANS, PERM_CONS_IFF]);

val PERM_LENGTH = Q.store_thm(
  "PERM_LENGTH",
  `!l1 l2. PERM l1 l2 ==> (LENGTH l1 = LENGTH l2)`,
  HO_MATCH_MP_TAC PERM_IND THEN SRW_TAC [][]);

val PERM_MEM_EQ = Q.store_thm(
  "PERM_MEM_EQ",
  `!l1 l2. PERM l1 l2 ==> !x. MEM x l1 = MEM x l2`,
  HO_MATCH_MP_TAC PERM_IND THEN SRW_TAC [][AC DISJ_ASSOC DISJ_COMM]);

local open pred_setTheory in
val PERM_LIST_TO_SET = store_thm(
"PERM_LIST_TO_SET",
``!l1 l2. PERM l1 l2 ==> (set l1 = set l2)``,
SRW_TAC[][EXTENSION,PERM_MEM_EQ])
end

(*---------------------------------------------------------------------------*
 * The idea of sortedness requires a "permutation" relation for lists, and   *
 * a "chain" predicate that holds just when the relation R holds between     *
 * all adjacent elements of the list.                                        *
 *---------------------------------------------------------------------------*)

val SORTED_DEF =
 Define
  `(SORTED R [] = T) /\
   (SORTED R [x] = T) /\
   (SORTED R (x::y::rst) = R x y /\ SORTED R (y::rst))`;


val SORTS_DEF =
 Define
    `SORTS f R = !l. PERM l (f R l) /\ SORTED R (f R l)`;


(*---------------------------------------------------------------------------*
 *    When consing onto a sorted list yields a sorted list                   *
 *---------------------------------------------------------------------------*)

val SORTED_EQ = Q.store_thm
("SORTED_EQ",
 `!R L x.
    transitive R ==> (SORTED R (x::L) = SORTED R L /\ !y. MEM y L ==> R x y)`,
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
    SORTED R (L1 ++ L2)`,
Induct_on `L1`
  THEN SRW_TAC [boolSimps.CONJ_ss][SORTED_EQ]
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
   PERM (L ++ (l1 ++ l2)) (a1 ++ a2)`,
Induct_on `L`
  THEN RW_TAC list_ss [PART_DEF, PERM_REFL]
  THEN RES_TAC THEN MATCH_MP_TAC PERM_TRANS THENL
  [Q.EXISTS_TAC `APPEND L (APPEND (h::l1) l2)`,
   Q.EXISTS_TAC `APPEND L (APPEND l1 (h::l2))`]
  THEN PROVE_TAC [APPEND,APPEND_ASSOC,CONS_PERM,PERM_REFL]);

(*---------------------------------------------------------------------------
     Everything in the partitions occurs in the original list, and
     vice-versa. The goal has been generalized.
 ---------------------------------------------------------------------------*)

val PART_MEM = Q.store_thm
("PART_MEM",
 `!P L a1 a2 l1 l2.
     ((a1,a2) = PART P L l1 l2)
       ==>
      !x. MEM x (L ++ (l1 ++ l2)) = MEM x (a1 ++ a2)`,
  METIS_TAC [PART_PERM, PERM_MEM_EQ]);

(*---------------------------------------------------------------------------
     A packaged version of PART. Most theorems about PARTITION
     will be instances of theorems about PART.
 ---------------------------------------------------------------------------*)

val PARTITION_DEF = Define`PARTITION P l = PART P l [] []`;


(*---------------------------------------------------------------------------*
 *      Quicksort                                                            *
 *---------------------------------------------------------------------------*)

val QSORT_DEF =
 tDefine
  "QSORT"
  `(QSORT ord [] = []) /\
   (QSORT ord (h::t) =
       let (l1,l2) = PARTITION (\y. ord y h) t
       in
         QSORT ord l1 ++ [h] ++ QSORT ord l2)`
 (WF_REL_TAC `measure (LENGTH o SND)`
     THEN RW_TAC list_ss [o_DEF,PARTITION_DEF]
     THEN IMP_RES_THEN MP_TAC PART_LENGTH_LEM
     THEN RW_TAC list_ss []);

val QSORT_IND = fetch "-" "QSORT_IND";

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
  THEN RW_TAC list_ss [QSORT_DEF,PERM_REFL,PARTITION_DEF]
  THEN REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
  THEN MATCH_MP_TAC CONS_PERM
  THEN MATCH_MP_TAC PERM_TRANS
  THEN Q.EXISTS_TAC `l1 ++ l2`
  THEN RW_TAC std_ss [] THENL
  [METIS_TAC [APPEND,APPEND_NIL,PART_PERM],
   METIS_TAC [PERM_CONG]]);


(*---------------------------------------------------------------------------
 * The result list is sorted.
 *---------------------------------------------------------------------------*)

val QSORT_SORTED =
Q.store_thm
("QSORT_SORTED",
`!R L. transitive R /\ total R ==> SORTED R (QSORT R L)`,
 recInduct QSORT_IND
  THEN RW_TAC bool_ss [QSORT_DEF, SORTED_DEF, PARTITION_DEF]
  THEN REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
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


(*---------------------------------------------------------------------------*)
(* Add the computable definitions to the database used by EVAL               *)
(*---------------------------------------------------------------------------*)

val _ =
 computeLib.add_persistent_funs ["QSORT_DEF"];



(*---------------------------------------------------------------------------
 * Theorems about Permutations. Added by Thomas Tuerk. 19 March 2009
 *---------------------------------------------------------------------------*)

val PERM_APPEND_IFF = store_thm ("PERM_APPEND_IFF",
``(!l:'a list l1 l2. PERM (l++l1) (l++l2) = PERM l1 l2) /\
  (!l:'a list l1 l2. PERM (l1++l) (l2++l) = PERM l1 l2)``,

   MATCH_MP_TAC (prove (``(a /\ (a ==> b)) ==> (a /\ b)``, PROVE_TAC[])) THEN
   Tactical.REVERSE CONJ_TAC THEN1 PROVE_TAC [PERM_APPEND, PERM_TRANS] THEN
   Induct_on `l` THEN ASM_SIMP_TAC list_ss [PERM_CONS_IFF]
);

val PERM_SINGLE_SWAP_DEF = Define `PERM_SINGLE_SWAP l1 l2 =
    ?x1 x2 x3. (l1 = x1 ++ x2 ++ x3) /\ (l2 = x1 ++ x3 ++ x2)`;


val PERM_SINGLE_SWAP_REFL = store_thm ("PERM_SINGLE_SWAP_REFL",
``!l. PERM_SINGLE_SWAP l l``,
  GEN_TAC THEN REWRITE_TAC [PERM_SINGLE_SWAP_DEF] THEN
  Q.EXISTS_TAC `l` THEN Q.EXISTS_TAC `[]` THEN Q.EXISTS_TAC `[]` THEN
  REWRITE_TAC[APPEND_NIL]);

val PERM_SINGLE_SWAP_SYM = store_thm ("PERM_SINGLE_SWAP_SYM",
``!l1 l2. PERM_SINGLE_SWAP l1 l2 = PERM_SINGLE_SWAP l2 l1``,
  PROVE_TAC[PERM_SINGLE_SWAP_DEF]);



val PERM_TC = store_thm ("PERM_TC",
    ``PERM = TC PERM_SINGLE_SWAP``,

SIMP_TAC std_ss [FUN_EQ_THM] THEN
REPEAT GEN_TAC THEN EQ_TAC THENL [
   Q.SPEC_TAC (`x'`, `l2`) THEN Q.SPEC_TAC (`x`, `l1`) THEN
   HO_MATCH_MP_TAC PERM_IND THEN
   REPEAT CONJ_TAC THENL [
      MATCH_MP_TAC TC_SUBSET THEN REWRITE_TAC[PERM_SINGLE_SWAP_REFL],

      GEN_TAC THEN
      MATCH_MP_TAC relationTheory.TC_lifts_monotonicities THEN
      SIMP_TAC std_ss [PERM_SINGLE_SWAP_DEF, GSYM LEFT_FORALL_IMP_THM] THEN
      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC `x::x1` THEN Q.EXISTS_TAC `x2` THEN Q.EXISTS_TAC `x3` THEN
      SIMP_TAC list_ss [],

      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC (CONJUNCT2 (SIMP_RULE std_ss [FORALL_AND_THM] TC_RULES)) THEN
      Q.EXISTS_TAC `y::x::l1` THEN
      CONJ_TAC THENL [
         Tactical.REVERSE (`PERM_SINGLE_SWAP (x::y::l1) ((y::l1) ++ [x]) /\
                            PERM_SINGLE_SWAP ((y::l1) ++ [x]) (y::x::l1)` by ALL_TAC) THEN1 (
           PROVE_TAC[TC_RULES]
         ) THEN
	 SIMP_TAC std_ss [PERM_SINGLE_SWAP_DEF] THEN
	 REPEAT STRIP_TAC THENL [
           Q.EXISTS_TAC `[]` THEN Q.EXISTS_TAC `[x]` THEN Q.EXISTS_TAC `y::l1` THEN
           SIMP_TAC list_ss [],

           Q.EXISTS_TAC `[y]` THEN Q.EXISTS_TAC `l1` THEN Q.EXISTS_TAC `[x]` THEN
           SIMP_TAC list_ss []
         ],


         POP_ASSUM MP_TAC THEN
         Q.SPEC_TAC (`l2`, `l2`) THEN Q.SPEC_TAC (`l1`, `l1`) THEN
         HO_MATCH_MP_TAC relationTheory.TC_lifts_monotonicities THEN
         SIMP_TAC list_ss [PERM_SINGLE_SWAP_DEF, GSYM LEFT_FORALL_IMP_THM] THEN
	 REPEAT STRIP_TAC THEN
         Q.EXISTS_TAC `y::x::x1` THEN Q.EXISTS_TAC `x2` THEN Q.EXISTS_TAC `x3` THEN
         SIMP_TAC list_ss []
      ],


      PROVE_TAC[TC_TRANSITIVE, transitive_def]
   ],


   Q.SPEC_TAC (`x'`, `l2`) THEN Q.SPEC_TAC (`x`, `l1`) THEN
   HO_MATCH_MP_TAC TC_INDUCT THEN
   REWRITE_TAC[PERM_TRANS] THEN
   SIMP_TAC std_ss [PERM_SINGLE_SWAP_DEF, GSYM LEFT_FORALL_IMP_THM,
                    PERM_APPEND_IFF, GSYM APPEND_ASSOC,
			 PERM_APPEND]
]);



val PERM_RTC = store_thm ("PERM_RTC",
    ``PERM = RTC PERM_SINGLE_SWAP``,

REWRITE_TAC[GSYM (CONJUNCT2 (SIMP_RULE std_ss [FORALL_AND_THM] TC_RC_EQNS)),
	    PERM_TC] THEN
AP_TERM_TAC THEN
SIMP_TAC std_ss [RC_DEF, FUN_EQ_THM] THEN
PROVE_TAC[PERM_SINGLE_SWAP_REFL]);


val PERM_EQC = store_thm ("PERM_EQC",
    ``PERM = EQC PERM_SINGLE_SWAP``,

`SC PERM_SINGLE_SWAP = PERM_SINGLE_SWAP` by ALL_TAC THEN1 (
   SIMP_TAC std_ss [FUN_EQ_THM, SC_DEF, PERM_SINGLE_SWAP_SYM]
) THEN
ASM_REWRITE_TAC[EQC_DEF, GSYM PERM_TC] THEN
SIMP_TAC std_ss [RC_DEF, FUN_EQ_THM] THEN
PROVE_TAC[PERM_REFL]);



val PERM_lift_TC_RULE =
  (GEN_ALL o
   SIMP_RULE std_ss [GSYM PERM_TC, PERM_SINGLE_SWAP_DEF, GSYM LEFT_FORALL_IMP_THM,
		     GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] o
   Q.ISPEC `PERM_SINGLE_SWAP` o
   Q.GEN `R`);


val PERM_lifts_transitive_relations = save_thm (
"PERM_lifts_transitive_relations",
PERM_lift_TC_RULE TC_lifts_transitive_relations);

val PERM_lifts_equalities = save_thm (
"PERM_lifts_equalities",
PERM_lift_TC_RULE TC_lifts_equalities);

val PERM_lifts_invariants = save_thm (
"PERM_lifts_invariants",
PERM_lift_TC_RULE TC_lifts_invariants);


val PERM_lifts_monotonicities = store_thm (
"PERM_lifts_monotonicities",
``!f. (!x1:'a list x2 x3. ?x1':'b list x2' x3'.
       (f (x1 ++ x2 ++ x3) = x1' ++ x2' ++ x3') /\
       (f (x1 ++ x3 ++ x2) = x1' ++ x3' ++ x2')) ==>
      !x y. PERM x y ==> PERM (f x) (f y)``,
GEN_TAC THEN STRIP_TAC THEN
MATCH_MP_TAC PERM_lifts_transitive_relations THEN
REWRITE_TAC[PERM_transitive] THEN
REPEAT GEN_TAC THEN
POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [`x1`,`x2`,`x3`])) THEN
ASM_REWRITE_TAC[PERM_APPEND, PERM_APPEND_IFF, GSYM APPEND_ASSOC]);


val PERM_EQUIVALENCE = store_thm (
"PERM_EQUIVALENCE",
``equivalence PERM``,
REWRITE_TAC [PERM_EQC, EQC_EQUIVALENCE]);

val PERM_EQUIVALENCE_ALT_DEF = store_thm(
"PERM_EQUIVALENCE_ALT_DEF",
``!x y. PERM x y = (PERM x = PERM y)``,
SIMP_TAC std_ss [GSYM ALT_equivalence,
		 PERM_EQUIVALENCE]);

val ALL_DISTINCT_PERM = store_thm ("ALL_DISTINCT_PERM",
   ``!l1 l2. PERM l1 l2 ==> (ALL_DISTINCT l1 = ALL_DISTINCT l2)``,
   MATCH_MP_TAC PERM_lifts_equalities THEN
   SIMP_TAC list_ss [ALL_DISTINCT_APPEND] THEN
   PROVE_TAC[]);


val PERM_ALL_DISTINCT = store_thm ("PERM_ALL_DISTINCT",
``!l1 l2. (ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\ (!x. MEM x l1 = MEM x l2)) ==>
           PERM l1 l2``,

SIMP_TAC std_ss [ALL_DISTINCT_FILTER, PERM_DEF, MEM_FILTER_EQ] THEN
METIS_TAC[]);

val ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST = store_thm(
"ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST",
``!ls. ALL_DISTINCT ls = PERM ls (SET_TO_LIST (set ls))``,
SRW_TAC[][EQ_IMP_THM] THEN1 (
  MATCH_MP_TAC PERM_ALL_DISTINCT THEN
  SRW_TAC[][] ) THEN
IMP_RES_TAC ALL_DISTINCT_PERM THEN
FULL_SIMP_TAC (srw_ss()) [])

val PERM_MAP = store_thm ("PERM_MAP",
``!f l1 l2. PERM l1 l2 ==> PERM (MAP f l1) (MAP f l2)``,
   GEN_TAC THEN
   MATCH_MP_TAC PERM_lifts_monotonicities THEN
   REWRITE_TAC[MAP_APPEND] THEN
   PROVE_TAC[]);

val PERM_SUM = Q.store_thm(
"PERM_SUM",
`!l1 l2. PERM l1 l2 ==> (SUM l1 = SUM l2)`,
HO_MATCH_MP_TAC PERM_IND THEN
SRW_TAC [][] THEN DECIDE_TAC);

val PERM_FILTER = store_thm ("PERM_FILTER",
``!P l1 l2. PERM l1 l2 ==> (PERM (FILTER P l1) (FILTER P l2))``,
   GEN_TAC THEN
   MATCH_MP_TAC PERM_lifts_monotonicities THEN
   REWRITE_TAC[FILTER_APPEND_DISTRIB] THEN
   PROVE_TAC []);

val PERM_REVERSE = Q.store_thm(
  "PERM_REVERSE",
  `PERM ls (REVERSE ls)`,
Induct_on `ls` THEN SRW_TAC [][] THEN
`PERM ([h] ++ REVERSE ls) (REVERSE ls ++ [h])`
by SRW_TAC [][PERM_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [PERM_CONS_IFF,PERM_TRANS]);

val PERM_REVERSE_EQ = store_thm(
  "PERM_REVERSE_EQ",
  ``(PERM (REVERSE l1) l2 = PERM l1 l2) /\
    (PERM l1 (REVERSE l2) = PERM l1 l2)``,
  METIS_TAC [PERM_TRANS, PERM_SYM, PERM_REVERSE]);
val _ = export_rewrites ["PERM_REVERSE_EQ"]

val FOLDR_PERM = store_thm ("FOLDR_PERM",
``!f l1 l2 e.
(ASSOC f /\ COMM f) ==>
((PERM l1 l2) ==>
(FOLDR f e l1 = FOLDR f e l2))``,

SIMP_TAC std_ss [RIGHT_FORALL_IMP_THM] THEN
GEN_TAC THEN STRIP_TAC THEN
HO_MATCH_MP_TAC PERM_IND THEN
SIMP_TAC list_ss [] THEN
PROVE_TAC[operatorTheory.ASSOC_DEF, operatorTheory.COMM_DEF]);

val PERM_SET_TO_LIST_count_COUNT_LIST = Q.store_thm(
"PERM_SET_TO_LIST_count_COUNT_LIST",
`PERM (SET_TO_LIST (count n)) (COUNT_LIST n)`,
MATCH_MP_TAC PERM_ALL_DISTINCT THEN
CONJ_TAC THEN1 (
  MATCH_MP_TAC ALL_DISTINCT_SET_TO_LIST THEN
  MATCH_ACCEPT_TAC pred_setTheory.FINITE_COUNT ) THEN
SRW_TAC [][rich_listTheory.COUNT_LIST_GENLIST,ALL_DISTINCT_GENLIST,MEM_GENLIST]);

val SUM_IMAGE_count_SUM_GENLIST = Q.store_thm(
"SUM_IMAGE_count_SUM_GENLIST",
`SIGMA f (count n) = SUM (GENLIST f n)`,
RW_TAC pure_ss [SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST,pred_setTheory.FINITE_COUNT] THEN
MATCH_MP_TAC PERM_SUM THEN
MATCH_MP_TAC PERM_TRANS THEN
Q.EXISTS_TAC `(MAP f (COUNT_LIST n))` THEN
CONJ_TAC THEN1 (
  MATCH_MP_TAC PERM_MAP THEN
  MATCH_ACCEPT_TAC PERM_SET_TO_LIST_count_COUNT_LIST ) THEN
MATCH_MP_TAC PERM_INTRO THEN
REWRITE_TAC [rich_listTheory.COUNT_LIST_GENLIST] THEN
REWRITE_TAC [MAP_GENLIST,combinTheory.I_o_ID]);

local open arithmeticTheory prim_recTheory pred_setTheory in
val SUM_IMAGE_count_MULT = Q.store_thm(
"SUM_IMAGE_count_MULT",
`(!m. m < n ==> (g m = SIGMA (\x. f (x + k * m)) (count k))) ==>
 (SIGMA f (count (k * n)) = SIGMA g (count n))`,
Induct_on `n` THEN1 (
  SIMP_TAC bool_ss [SUM_IMAGE_THM,MULT_0,COUNT_ZERO] ) THEN
FULL_SIMP_TAC bool_ss
[MULT_SUC,SUM_IMAGE_count_SUM_GENLIST,GENLIST_APPEND,
 SUM_APPEND,GENLIST,SUM_SNOC] THEN
METIS_TAC [LESS_SUC,LESS_SUC_REFL])

val sum_of_sums = Q.store_thm(
"sum_of_sums",
`SIGMA (\m. SIGMA (f m) (count a)) (count b) = SIGMA (\m. f (m DIV a) (m MOD a)) (count (a * b))`,
Cases_on `a=0` THEN SRW_TAC [][SUM_IMAGE_THM,SUM_IMAGE_ZERO] THEN
Cases_on `b=0` THEN SRW_TAC [][SUM_IMAGE_THM,SUM_IMAGE_ZERO] THEN
MATCH_MP_TAC EQ_SYM THEN
MATCH_MP_TAC SUM_IMAGE_count_MULT THEN
SRW_TAC [][] THEN
MATCH_MP_TAC SUM_IMAGE_CONG THEN
SRW_TAC [][] THEN
METIS_TAC [ADD_SYM,MULT_SYM,DIV_MULT,MOD_MULT])
end

val SORTED_NIL = store_thm(
"SORTED_NIL",
``!R. SORTED R []``,
SRW_TAC[][SORTED_DEF])
val _ = export_rewrites["SORTED_NIL"]

val SORTED_SING = store_thm(
"SORTED_SING",
``!R x. SORTED R [x]``,
SRW_TAC[][SORTED_DEF])
val _ = export_rewrites["SORTED_SING"]

val SORTED_EL_SUC = store_thm(
"SORTED_EL_SUC",
``!R ls. SORTED R ls =
        !n. (SUC n) < LENGTH ls ==>
            R (EL n ls) (EL (SUC n) ls)``,
GEN_TAC THEN Induct THEN SRW_TAC[][] THEN
Cases_on `ls` THEN SRW_TAC[][SORTED_DEF] THEN
SRW_TAC[][EQ_IMP_THM] THEN1 (
  Cases_on `n` THEN SRW_TAC[][] THEN
  FULL_SIMP_TAC (srw_ss()) [] )
THEN1 (
  POP_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
  SRW_TAC[][] ) THEN
FIRST_X_ASSUM (Q.SPEC_THEN `SUC n` MP_TAC) THEN
SRW_TAC [][])

val SORTED_EL_LESS = store_thm(
"SORTED_EL_LESS",
``!R. transitive R ==>
  !ls. SORTED R ls =
       !m n. m < n /\ n < LENGTH ls ==>
             R (EL m ls) (EL n ls)``,
GEN_TAC THEN STRIP_TAC THEN
Induct THEN SRW_TAC[][] THEN
SRW_TAC[][SORTED_EQ,EQ_IMP_THM] THEN1 (
  Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `m` THEN SRW_TAC[][] THEN1
    METIS_TAC[MEM_EL] THEN
  FULL_SIMP_TAC (srw_ss()) [] )
THEN1 (
  FIRST_X_ASSUM (Q.SPECL_THEN [`SUC m`,`SUC n`] MP_TAC) THEN
  SRW_TAC [][] ) THEN
FULL_SIMP_TAC (srw_ss()) [MEM_EL] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`0`,`SUC n`] MP_TAC) THEN
SRW_TAC [][])

val SORTED_transitive_APPEND_IFF = store_thm(
"SORTED_transitive_APPEND_IFF",
``!R. transitive R ==>
  !L1 L2. SORTED R (L1 ++ L2) =
          SORTED R L1 /\ SORTED R L2 /\
          ((L1 = []) \/ (L2 = []) \/ (R (LAST L1) (HD L2)))``,
GEN_TAC THEN STRIP_TAC THEN
Induct THEN SRW_TAC[][] THEN
SRW_TAC[][SORTED_EQ] THEN
Cases_on `L1` THEN SRW_TAC[][] THEN1 (
  SRW_TAC[][EQ_IMP_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    Cases_on `L2` THEN FULL_SIMP_TAC (srw_ss()) [] ) THEN
  Q.PAT_ASSUM `SORTED R L2` MP_TAC THEN
  SRW_TAC[][SORTED_EL_LESS] THEN
  FULL_SIMP_TAC (srw_ss()) [MEM_EL,transitive_def] THEN
  Cases_on `n` THEN1 SRW_TAC[][] THEN
  METIS_TAC[prim_recTheory.LESS_0,EL] ) THEN
SRW_TAC[][GSYM CONJ_ASSOC] THEN
Q.MATCH_ABBREV_TAC `P1 /\ P2 /\ P3 /\ P4 = P1 /\ P6 /\ P2 /\ P3` THEN
Q_TAC SUFF_TAC `P1 /\ P2 /\ P3 ==> (P4 = P6)` THEN1 SRW_TAC[][EQ_IMP_THM] THEN
UNABBREV_ALL_TAC THEN SRW_TAC[][] THEN1 SRW_TAC[][] THEN
EQ_TAC THEN1 METIS_TAC[] THEN
STRIP_TAC THEN Q.X_GEN_TAC `x` THEN
REVERSE (Cases_on `MEM x L2`) THEN1 METIS_TAC[] THEN
Q.MATCH_ASSUM_RENAME_TAC `R (LAST (y::t)) (HD L2)` [] THEN
`R h (LAST (y::t))` by (
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  Cases_on `t` THEN1 SRW_TAC[][] THEN
  SIMP_TAC bool_ss [LAST_CONS,rich_listTheory.MEM_LAST] ) THEN
`R h (EL 0 L2)` by METIS_TAC [transitive_def,EL] THEN
Q.PAT_ASSUM `MEM x L2` MP_TAC THEN
SRW_TAC[][MEM_EL] THEN
Cases_on `n` THEN1 SRW_TAC[][] THEN
METIS_TAC [prim_recTheory.LESS_0,SORTED_EL_LESS,transitive_def])

val MEM_PERM =
  store_thm(
    "MEM_PERM",
    ``!l1 l2. PERM l1 l2 ==> (!a. MEM a l1 = MEM a l2)``,
    METIS_TAC [Q.SPEC `$= a` MEM_FILTER, PERM_DEF]);

val SORTED_PERM_EQ = store_thm(
"SORTED_PERM_EQ",
``!R. transitive R /\ antisymmetric R ==>
  !l1 l2. SORTED R l1 /\ SORTED R l2 /\ PERM l1 l2 ==> (l1 = l2)``,
GEN_TAC THEN STRIP_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
SRW_TAC[][SORTED_EQ,PERM_CONS_EQ_APPEND] THEN
`!x. MEM x M ==> (x = h)` by (
  Q.PAT_ASSUM `SORTED R (aa++bb)` MP_TAC THEN
  SRW_TAC[][SORTED_transitive_APPEND_IFF] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `R h x` by METIS_TAC [MEM_PERM,MEM_APPEND] THEN
  Cases_on `M = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  FULL_SIMP_TAC (srw_ss()) [LAST_EL,MEM_EL] THEN
  `R x h` by (
    Cases_on `n = PRE (LENGTH M)` THEN1 SRW_TAC[][] THEN
    `n < PRE (LENGTH M)` by DECIDE_TAC THEN
    `PRE (LENGTH M) < LENGTH M` by DECIDE_TAC THEN
    METIS_TAC [SORTED_EL_LESS,transitive_def] ) THEN
  METIS_TAC [antisymmetric_def] ) THEN
`M ++ [h] = h::M` by (
  POP_ASSUM MP_TAC THEN
  Q.ID_SPEC_TAC `h` THEN
  REPEAT (POP_ASSUM (K ALL_TAC)) THEN
  Induct_on `M` THEN SRW_TAC[][] ) THEN
SRW_TAC[][] THEN
FIRST_X_ASSUM MATCH_MP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.PAT_ASSUM `SORTED R (h::N)` MP_TAC THEN
SRW_TAC[][SORTED_EQ])

val QSORT_eq_if_PERM = store_thm(
"QSORT_eq_if_PERM",
``!R. total R /\ transitive R /\ antisymmetric R ==>
  !l1 l2. (QSORT R l1 = QSORT R l2) = PERM l1 l2``,
PROVE_TAC[QSORT_PERM,QSORT_SORTED,SORTED_PERM_EQ,PERM_TRANS,PERM_SYM])

(*Perm theorems for the simplication*)

val PERM_FUN_APPEND = store_thm (
"PERM_FUN_APPEND",
``!l1 l1' l2 l2'.
(PERM l1 = PERM l1') ==>
(PERM l2 = PERM l2') ==>
(PERM (l1 ++ l2) = PERM (l1' ++ l2'))``,

SIMP_TAC std_ss [GSYM PERM_EQUIVALENCE_ALT_DEF,
                 PERM_CONG]);


val PERM_FUN_CONS = store_thm (
"PERM_FUN_CONS",
``!x l1 l1'.
(PERM l1 = PERM l1') ==>
(PERM (x::l1) = PERM (x::l1'))``,

SIMP_TAC std_ss [GSYM PERM_EQUIVALENCE_ALT_DEF,
                 PERM_CONS_IFF]);


val PERM_FUN_APPEND_CONS = store_thm (
"PERM_FUN_APPEND_CONS",
``!x l1 l2. PERM (l1 ++ x::l2) = PERM (x::l1++l2)``,
METIS_TAC[PERM_EQUIVALENCE_ALT_DEF,
          PERM_APPEND, PERM_CONS_IFF,
          APPEND])


val PERM_FUN_SWAP_AT_FRONT = store_thm (
"PERM_FUN_SWAP_AT_FRONT",
``!x y l. PERM (x::y::l) = PERM (y::x::l)``,
REWRITE_TAC[GSYM PERM_EQUIVALENCE_ALT_DEF,
	    PERM_SWAP_AT_FRONT, PERM_REFL]);

val PERM_FUN_CONS_11_SWAP_AT_FRONT = store_thm (
"PERM_FUN_CONS_11_SWAP_AT_FRONT",
``!y l1 x l2.
(PERM l1 = PERM (x::l2)) ==>
(PERM (y::l1) = PERM (x::y::l2))``,

REPEAT STRIP_TAC THEN
ASSUME_TAC (Q.SPECL [`x`, `y`,`l2`] PERM_FUN_SWAP_AT_FRONT) THEN
ASM_REWRITE_TAC[] THEN
FULL_SIMP_TAC std_ss [GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_CONS_IFF]);


val PERM_FUN_CONS_11_APPEND = store_thm (
"PERM_FUN_CONS_11_APPEND",
``!y l1 l2 l3.
(PERM l1 = PERM (l2++l3)) ==>
(PERM (y::l1) = PERM (l2++(y::l3)))``,

REPEAT STRIP_TAC THEN
REWRITE_TAC[PERM_FUN_APPEND_CONS] THEN
FULL_SIMP_TAC std_ss [GSYM PERM_EQUIVALENCE_ALT_DEF,
                      PERM_CONS_IFF, APPEND]);




val PERM_FUN_CONS_APPEND_1 = store_thm (
"PERM_FUN_CONS_APPEND_1",
``!l l1 x l2.
(PERM l1 = PERM (x::l2)) ==>
(PERM (l1 ++ l) = PERM (x::(l2++l)))``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`l1`, `l`, `x::l2`,`l`] PERM_CONG) THEN
ASM_REWRITE_TAC[PERM_EQUIVALENCE_ALT_DEF, APPEND]);


val PERM_FUN_CONS_APPEND_2 = store_thm (
"PERM_FUN_CONS_APPEND_2",
``!l l1 x l2.
(PERM l1 = PERM (x::l2)) ==>
(PERM (l ++ l1) = PERM (x::(l ++ l2)))``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`l`,`l1`,`l`, `x::l2`] PERM_CONG) THEN
ASM_REWRITE_TAC[PERM_EQUIVALENCE_ALT_DEF,APPEND,
		PERM_FUN_APPEND_CONS]);


val PERM_FUN_APPEND_APPEND_1 = store_thm (
"PERM_FUN_APPEND_APPEND_1",
``!l1 l2 l3 l4.
(PERM l1 = PERM (l2++l3)) ==>
(PERM (l1 ++ l4) = PERM (l2++(l3++l4)))``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`l1`, `l4`, `l2++l3`, `l4`] PERM_CONG) THEN
ASM_REWRITE_TAC[PERM_EQUIVALENCE_ALT_DEF, APPEND_ASSOC]);


val PERM_FUN_APPEND_APPEND_2 = store_thm (
"PERM_FUN_APPEND_APPEND_2",
``!l1 l2 l3 l4.
(PERM l1 = PERM (l2++l3)) ==>
(PERM (l4 ++ l1) = PERM (l2++(l4++l3)))``,

REPEAT STRIP_TAC THEN
ASSUME_TAC (Q.SPECL [`l4`, `l1`, `l4`, `l2++l3`] PERM_CONG) THEN
FULL_SIMP_TAC std_ss [PERM_EQUIVALENCE_ALT_DEF, APPEND_ASSOC] THEN
REWRITE_TAC[GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_APPEND_IFF,
	    PERM_APPEND]);


val PERM_FUN_APPEND = store_thm (
"PERM_FUN_APPEND",
``!l1 l2. PERM (l1 ++ l2) = PERM (l2 ++ l1)``,
REWRITE_TAC[GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_APPEND])


val PERM_FUN_CONS_IFF = store_thm (
"PERM_FUN_CONS_IFF",
``!x l1 l2. (PERM l1 = PERM l2) ==> (PERM (x::l1) = PERM (x::l2))``,
REWRITE_TAC[GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_CONS_IFF]);



val PERM_FUN_APPEND_IFF = store_thm (
"PERM_FUN_APPEND_IFF",
``!l l1 l2. (PERM l1 = PERM l2) ==> (PERM (l++l1) = PERM (l++l2))``,
REWRITE_TAC[GSYM PERM_EQUIVALENCE_ALT_DEF, PERM_APPEND_IFF]);



val PERM_FUN_CONG = store_thm (
"PERM_FUN_CONG",
``!l1 l1' l2 l2'.
(PERM l1 = PERM l1') ==>
(PERM l2 = PERM l2') ==>
(PERM l1 l2 = PERM l1' l2')``,
METIS_TAC[PERM_EQUIVALENCE_ALT_DEF])


val PERM_CONG_2 = store_thm (
"PERM_CONG_2",
``!l1 l1' l2 l2'.
(PERM l1 l1') ==>
(PERM l2 l2') ==>
(PERM l1 l2 = PERM l1' l2')``,
METIS_TAC[PERM_EQUIVALENCE_ALT_DEF])


val PERM_CONG_APPEND_IFF = store_thm (
"PERM_CONG_APPEND_IFF",
``!l l1 l1' l2 l2'.
(PERM l1 (l++l1')) ==>
(PERM l2 (l++l2')) ==>
(PERM l1 l2 = PERM l1' l2')``,
METIS_TAC [PERM_EQUIVALENCE_ALT_DEF, PERM_APPEND_IFF]);


val PERM_FUN_SPLIT = store_thm (
"PERM_FUN_SPLIT",
``!l l1 l1' l2.
(PERM l (l1++l2)) ==>
(PERM l1' l1) ==>
(PERM l (l1'++l2))``,
METIS_TAC [PERM_EQUIVALENCE_ALT_DEF, PERM_APPEND_IFF]);


val PERM_REWR = store_thm (
"PERM_REWR",
``!l r l1 l2.
(PERM l r) ==>
(PERM (l++l1) l2 = PERM (r++l1) l2)``,
PROVE_TAC [PERM_EQUIVALENCE_ALT_DEF, PERM_APPEND_IFF]);

(*---------------------------------------------------------------------------*)
(* QSORT3 - A stable version of QSORT (James Reynolds - 10/2010)             *)
(*    Lists are stable if filtering using any predicate that implies two     *)
(*    elements are unordered is unaffected by sorting.                       *)
(*---------------------------------------------------------------------------*)

val STABLE_DEF = Define `
    STABLE sort r =
    SORTS sort r /\
    !p. (!x y. p x /\ p y ==> r x y) ==>
        (!l. FILTER p l = FILTER p (sort r l))`;

(*---------------------------------------------------------------------------*)
(* PART3 - Split a list into < h, = h and > h                                *)
(*---------------------------------------------------------------------------*)

val PART3_DEF = Define `
    (PART3 R h [] = ([],[],[])) /\
    (PART3 R h (hd::tl) =
         if R h hd /\ R hd h
	    then (I ## CONS hd ## I) (PART3 R h tl)
	    else if R hd h
                    then (CONS hd ## I ## I) (PART3 R h tl)
		    else (I ## I ## CONS hd) (PART3 R h tl))`;

val LENGTH_FILTER =
  prove(``!a. LENGTH (FILTER P a) <= LENGTH a``,
    Induct THEN RW_TAC arith_ss [FILTER, LENGTH]);

val length_lem =
  prove(``!a h. LENGTH (FILTER P a) < LENGTH (h::a)``,
    REPEAT STRIP_TAC THEN REWRITE_TAC [LENGTH] THEN
    MATCH_MP_TAC (DECIDE ``!a b. a <= b ==> a < SUC b``) THEN
    MATCH_ACCEPT_TAC LENGTH_FILTER);

(*---------------------------------------------------------------------------*)
(* PART3_FILTER - Partition is the same as filtering.                        *)
(*---------------------------------------------------------------------------*)

val PART3_FILTER =
  store_thm("PART3_FILTER",
    ``!tl hd. PART3 R hd tl = (FILTER (\x. R x hd /\ ~R hd x) tl,
                            FILTER (\x. R x hd /\ R hd x) tl,
                            FILTER (\x. ~R x hd) tl)``,
    Induct THEN RW_TAC std_ss [PART3_DEF, PAIR_MAP, FILTER] THEN
    FULL_SIMP_TAC std_ss []);

(*---------------------------------------------------------------------------*)
(* QSORT3 - Partition three ways but only recurse on < and >                 *)
(*---------------------------------------------------------------------------*)

val QSORT3_DEF = tDefine "QSORT3" `
    (QSORT3 R [] = []) /\
    (QSORT3 R (hd::tl) =
    	let (lo,eq,hi) = PART3 R hd tl
        in QSORT3 R lo ++ (hd::eq) ++ QSORT3 R hi)`
  (WF_REL_TAC `measure (LENGTH o SND)` THEN
   RW_TAC arith_ss [PART3_FILTER, length_lem]);

val PERM3 =
  store_thm(
    "PERM3",
    ``!x a a' b b' c c'.
      (PERM a a' /\ PERM b b' /\ PERM c c') /\ PERM x (a ++ b ++ c)
      ==> PERM x (a' ++ b' ++ c')``,
    RW_TAC std_ss [PERM_DEF, FILTER_APPEND_DISTRIB]);

val PULL_CONV = REPEATC (DEPTH_CONV (RIGHT_IMP_FORALL_CONV ORELSEC AND_IMP_INTRO_CONV));
val PULL_RULE = CONV_RULE PULL_CONV;

val IND_STEP_TAC = PAT_ASSUM ``!y. P ==> Q`` (MATCH_MP_TAC o PULL_RULE);

val tospec =
    Q.GEN `P`
      (MATCH_MP (SPEC_ALL
        (REWRITE_RULE [GSYM AND_IMP_INTRO] PERM_TRANS)) (SPEC_ALL PERM_SPLIT));

val filter_filter =
  prove(
    ``!l P Q. FILTER P (FILTER Q l) = FILTER (\x. P x /\ Q x) l``,
    Induct THEN NTAC 2 (RW_TAC std_ss [FILTER]) THEN PROVE_TAC []);

val PERM3_FILTER =
  store_thm(
    "PERM3_FILTER",
    ``!l h. PERM l
      (FILTER (\x. R x h /\ ~R h x) l ++ FILTER (\x. R x h /\ R h x) l ++
       FILTER (\x. ~R x h) l)``,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (SPEC ``\x. (R:'a -> 'a -> bool) x h`` tospec) THEN
    REWRITE_TAC [APPEND_ASSOC] THEN MATCH_MP_TAC PERM_CONG THEN
    RW_TAC std_ss [combinTheory.o_DEF, PERM_REFL] THEN
    MATCH_MP_TAC (SPEC ``(R :'a -> 'a -> bool) h`` tospec) THEN
    RW_TAC std_ss [combinTheory.o_DEF, PERM_REFL, filter_filter, FILTER_APPEND_DISTRIB] THEN
    MATCH_MP_TAC (PROVE [PERM_APPEND] ``(A = C) /\ (B = D) ==> (PERM (A ++ B) (D ++ C))``) THEN
    REPEAT CONJ_TAC THEN REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN PROVE_TAC []);

val PERM_QSORT3 =
  store_thm(
    "PERM_QSORT3",
    ``!l R. PERM l (QSORT3 R l)``,
    completeInduct_on `LENGTH l` THEN Cases THEN
    RW_TAC std_ss [PERM_CONS_EQ_APPEND, QSORT3_DEF, PERM_NIL, PART3_FILTER] THEN
    Q.EXISTS_TAC `QSORT3 R (FILTER (\x. R x h /\ ~R h x) t)` THEN
    Q.EXISTS_TAC `FILTER (\x. R x h /\ R h x) t ++ QSORT3 R (FILTER (\x. ~R x h) t) ` THEN
    RW_TAC std_ss [APPEND_ASSOC, GSYM APPEND] THEN
    MATCH_MP_TAC PERM3 THEN
    MAP_EVERY Q.EXISTS_TAC [
      `FILTER (\x. R x h /\ ~R h x) t`,
      `FILTER (\x. R x h /\ R h x) t`,
      `FILTER (\x. ~R x h) t`] THEN
    RW_TAC std_ss [PERM_REFL] THEN TRY IND_STEP_TAC THEN RW_TAC arith_ss [length_lem] THEN
    METIS_TAC [PERM3_FILTER]);

val SORTED_EQ_PART =
  store_thm(
    "SORTED_EQ_PART",
    ``!l R. transitive R ==> SORTED R (FILTER (\x. R x hd /\ R hd x) l)``,
    Induct THEN REPEAT STRIP_TAC THEN
    RW_TAC std_ss [SORTED_DEF, FILTER, SORTED_EQ, MEM_FILTER] THEN
    PROVE_TAC [relationTheory.transitive_def]);

val QSORT3_SORTS =
  store_thm(
    "QSORT3_SORTS",
    ``!R. transitive R /\ total R ==> SORTS QSORT3 R``,
    RW_TAC std_ss [SORTS_DEF, PERM_QSORT3] THEN
    completeInduct_on `LENGTH l` THEN
    Cases_on `l` THEN
    RW_TAC std_ss [QSORT3_DEF, SORTED_DEF, PART3_FILTER] THEN
    REPEAT (MATCH_MP_TAC SORTED_APPEND THEN REPEAT CONJ_TAC) THEN
    ASM_REWRITE_TAC [] THEN
    TRY IND_STEP_TAC THEN
    RW_TAC std_ss [length_lem, SORTED_EQ, MEM_FILTER, SORTED_EQ_PART, MEM, MEM_FILTER, MEM_APPEND] THEN
    IMP_RES_TAC (PROVE [MEM_PERM, PERM_QSORT3] ``MEM x (QSORT3 R b) ==> MEM x b``) THEN
    FULL_SIMP_TAC std_ss [MEM_FILTER] THEN
    PROVE_TAC [relationTheory.total_def,relationTheory.transitive_def]);

val LENGTH_QSORT3 = PROVE [PERM_LENGTH, PERM_QSORT3] ``!l R. LENGTH (QSORT3 R l) = LENGTH l``;

fun SPLIT_APPEND_TAC x =
    MATCH_MP_TAC (prove(x, REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [APPEND_ASSOC])) THEN REPEAT CONJ_TAC

fun LIND_STEP (a,goal) =
  FIRST_ASSUM
    (CONV_TAC o LAND_CONV o REWR_CONV o SIMP_RULE std_ss [length_lem,LENGTH_QSORT3] o
     SPEC (mk_comb(``LENGTH:'a list -> num``,lhs goal)) o
     Q.GEN `m` o C (PART_MATCH (lhs o rand)) (lhs goal) o PULL_RULE) (a,goal)

val FILTER_P =
  prove(
    ``!R h. p h /\ transitive R /\ total R /\ (!x y. p x /\ p y ==> R x y) ==>
             !l. (FILTER (\x. p x /\ R x h /\ R h x) l = FILTER p l) /\
                 (FILTER p (FILTER (\x. R x h /\ ~R h x) l) = []) /\
                 (FILTER p (FILTER (\x. ~R x h) l) = [])``,
    NTAC 3 STRIP_TAC THEN Induct THEN RW_TAC std_ss [FILTER] THEN
    PROVE_TAC [relationTheory.transitive_def, relationTheory.total_def]);

val QSORT3_SPLIT =
  store_thm(
   "QSORT3_SPLIT",
   ``!R. transitive R /\ total R ==> !l e.
         QSORT3 R l = QSORT3 R (FILTER (\x. R x e /\ ~R e x) l) ++
                      FILTER (\x. R x e /\ R e x) l ++
                      QSORT3 R (FILTER (\x. ~R x e) l)``,
   NTAC 2 STRIP_TAC THEN completeInduct_on `LENGTH l` THEN Cases THEN
   RW_TAC std_ss [FILTER, QSORT3_DEF, PART3_FILTER, APPEND, APPEND_ASSOC] THEN
   RW_TAC std_ss [filter_filter, QSORT3_DEF, PART3_FILTER] THEN
   FULL_SIMP_TAC bool_ss [APPEND_ASSOC] THENL [
     SPLIT_APPEND_TAC ``(a = d) /\ (b = e) /\ (c = f ++ g ++ h) ==> (a ++ b ++ c = d ++ e ++ f ++ g ++ h)``,
     SPLIT_APPEND_TAC ``(a = d) /\ (b = e) /\ (c = f) ==> (a ++ b ++ c = d ++ e ++ f)``,
     SPLIT_APPEND_TAC ``(a = d ++ e ++ f) /\ (b = g) /\ (c = h) ==> (a ++ b ++ c = d ++ e ++ f ++ g ++ h)``] THEN
  TRY (LIND_STEP THEN SPLIT_APPEND_TAC ``(a = d) /\ (b = e) /\ (c = f) ==> (a ++ b ++ c = d ++ e ++ f)``) THEN
  RW_TAC std_ss [filter_filter] THEN
  REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  PROVE_TAC [relationTheory.total_def,relationTheory.transitive_def]);

(*---------------------------------------------------------------------------*)
(* Final proof: QSORT3 is a stable sort.                                     *)
(*---------------------------------------------------------------------------*)

val QSORT3_STABLE =
  store_thm(
    "QSORT3_STABLE",
    ``!R. transitive R /\ total R ==> STABLE QSORT3 R``,
    RW_TAC std_ss [STABLE_DEF, QSORT3_SORTS] THEN
    completeInduct_on `LENGTH l` THEN Cases_on `l` THEN
    RW_TAC std_ss [QSORT3_DEF, FILTER, PART3_FILTER] THEN
    RW_TAC std_ss [FILTER_APPEND_DISTRIB, filter_filter, GSYM APPEND, FILTER] THEN1
         METIS_TAC [FILTER_P, APPEND_NIL, length_lem, CONJUNCT1 APPEND] THEN
    MATCH_MP_TAC EQ_TRANS THEN Q.EXISTS_TAC `FILTER p (QSORT3 R t)` THEN CONJ_TAC THEN1
         (IND_STEP_TAC THEN RW_TAC arith_ss [LENGTH]) THEN
    METIS_TAC [FILTER_APPEND_DISTRIB, filter_filter, QSORT3_SPLIT]);

val _ = export_theory();

end;
