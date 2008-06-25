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
                              !h. perm (h::l1) (M ++ h::N)``,
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
 computeLib.add_persistent_funs [("QSORT_DEF",QSORT_DEF)];

val _ = export_theory();

(*---------------------------------------------------------------------------*)
(* Generate ML corresponding to the computable definitions.                  *)
(*---------------------------------------------------------------------------*)

val _ =
 let open EmitML
 in emitML (!Globals.emitMLDir)
    ("sorting",
       [OPEN ["list"],
        DEFN PART_DEF,
        DEFN PARTITION_DEF,
        DEFN QSORT_DEF,
        DEFN SORTED_DEF])
 end;

end;
