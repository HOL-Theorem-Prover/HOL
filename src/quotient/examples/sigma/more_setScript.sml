(* --------------------------------------------------------------------- *)
(* Boilerplate.                                                          *)
(* --------------------------------------------------------------------- *)
open HolKernel Parse boolLib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;


(* --------------------------------------------------------------------- *)
(* Create the theory.                                                    *)
(* --------------------------------------------------------------------- *)
val _ = new_theory "more_set";


(*
app load ["pairTheory", "listTheory",
          "arithmeticTheory", "pred_setTheory",
          "Num_induct", "listLib", "pred_setLib"];
*)

(* --------------------------------------------------------------------- *)
(* Autoload definitions and theorems from ancestor theories.             *)
(* --------------------------------------------------------------------- *)
open prim_recTheory;
open combinTheory;
open pairTheory;
open listTheory;
open arithmeticTheory;
open pred_setTheory;


(* --------------------------------------------------------------------- *)
(* Need the induction, list, and pred_set libraries.                     *)
(* --------------------------------------------------------------------- *)
open numLib;
open listLib;
open pred_setLib;


(* For errors try     <exp> handle e => Raise e;
*)


open tactics;



val IN_NOT_IN = store_thm
   ("IN_NOT_IN",
    (--`!s (x:'a) y. (x IN s) /\ ~(y IN s) ==> ~(x = y)`--),
    REPEAT STRIP_TAC
    THEN POP_ASSUM REWRITE_ALL_THM
    THEN RES_TAC
   );

val NOT_IN_SUBSET =
 store_thm
  ("NOT_IN_SUBSET",
   (--`!s t (x:'a). ~(x IN s) /\ (t SUBSET s) ==> ~(x IN t)`--),
   REPEAT STRIP_TAC
   THEN IMP_RES_TAC SUBSET_DEF
   THEN RES_TAC
  );


val IN_DISJOINT_IMP =
 store_thm
  ("IN_DISJOINT_IMP",
   (--`!s t (x:'a). DISJOINT s t ==>
           ((x IN s ==> ~(x IN t)) /\
            (x IN t ==> ~(x IN s)))`--),
   REWRITE_TAC[DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY]
   THEN REPEAT STRIP_TAC
   THENL
     [ POP_ASSUM (fn th1 => POP_ASSUM (fn th2 =>
                      MP_TAC (CONJ th2 th1) )),

       POP_ASSUM (fn th1 => POP_ASSUM (fn th2 =>
                      MP_TAC (CONJ th1 th2) ))
     ]
   THEN MATCH_MP_TAC F_IMP
   THEN ASM_REWRITE_TAC[]
  );


val CONJ_11 =
 store_thm
  ("CONJ_11",
   (--`!a b c d. (a = b) /\ (c = d) ==> (a /\ c = b /\ d)`--),
   REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]
  );


val MAP_I =
 store_thm
  ("MAP_I",
   (--`!lst:('a)list. MAP I lst = lst`--),
   LIST_INDUCT_TAC
   THEN ASM_REWRITE_TAC[MAP,I_THM]
  );

val APPEND_LENGTH_EQ = rich_listTheory.APPEND_LENGTH_EQ;

val APPEND_11 =
 store_thm
  ("APPEND_11",
   (--`!l1 l2 l3 l4:('a)list.
      (LENGTH l3 = LENGTH l1) /\ (LENGTH l4 = LENGTH l2) ==>
      ((APPEND l1 l2 = APPEND l3 l4) = ((l1 = l3) /\ (l2 = l4)))`--),
   PURE_ONCE_REWRITE_TAC[EQ_SYM_EQ]
   THEN REPEAT STRIP_TAC
   THEN PURE_ONCE_REWRITE_TAC[EQ_SYM_EQ]
   THEN IMP_RES_TAC APPEND_LENGTH_EQ
  );


val NULL_APPEND =
 store_thm
  ("NULL_APPEND",
   (--`!l1 l2:('a) list.
      NULL (APPEND l1 l2) =  NULL l1 /\ NULL l2`--),
   LIST_INDUCT_TAC
   THEN REWRITE_TAC[NULL,APPEND]
  );


val ONE_ONE =
 store_thm
  ("ONE_ONE",
   (--`!f:'a->'b.
      ONE_ONE f =
      (!x1 x2. (f x1 = f x2) = (x1 = x2))`--),
   REWRITE_TAC[ONE_ONE_THM]
   THEN GEN_TAC
   THEN EQ_TAC
   THENL
     [  REPEAT STRIP_TAC
        THEN EQ_TAC
        THEN DISCH_TAC
        THENL
          [  RES_TAC,
             ASM_REWRITE_TAC[]
          ],

        DISCH_TAC
        THEN ASM_REWRITE_TAC[]
     ]
  );


val ONTO_INVERSE =
 store_thm
  ("ONTO_INVERSE",
   (--`!(ss:'a->'b) y.
      ONTO ss  ==> (ss(@z. ss z = y) = y)`--),
   REWRITE_TAC[ONTO_THM]
   THEN REPEAT STRIP_TAC
   THEN CONV_TAC SELECT_CONV
   THEN ONCE_REWRITE_TAC[EQ_SYM_EQ]
   THEN ASM_REWRITE_TAC[]
  );

val o_ONTO_11 =
 store_thm
  ("o_ONTO_11",
   (--`!(ss:'a->'b) (s1:'b->'c) s2.
      ONTO ss ==> ((s2 o ss = s1 o ss) = (s2 = s1))`--),
   REPEAT STRIP_TAC
   THEN EQ_TAC
   THENL
     [  DISCH_TAC
        THEN EXT_TAC (--`y:'b`--)
        THEN GEN_TAC
        THEN POP_ASSUM (fn th =>
                 ASSUME_TAC (AP_THM th (--`@z. (ss:'a->'b) z = y`--)))
        THEN UNDISCH_LAST_TAC
        THEN IMP_RES_TAC ONTO_INVERSE
        THEN ASM_REWRITE_TAC[o_THM],

        DISCH_THEN REWRITE_THM
     ]
  );


val o_ONTO_IMP_11 =
 store_thm
  ("o_ONTO_IMP_11",
   (--`!(ss:'a->'b) (s1:'b->'c) s2.
      ONTO ss /\ (s2 o ss = s1 o ss) ==> (s2 = s1)`--),
   REPEAT STRIP_TAC
   THEN IMP_RES_TAC o_ONTO_11
  );

val o_INVERSE =
 store_thm
  ("o_INVERSE",
   (--`!(ss:'a->'b).
      ONE_ONE ss /\ ONTO ss ==>
      (ss o (\y. @z. ss z = y) = I) /\
      ((\y. @z. ss z = y) o ss = I)`--),
   REWRITE_TAC[ONE_ONE]
   THEN REPEAT STRIP_TAC
   THENL [ EXT_TAC (--`x:'b`--), EXT_TAC (--`x:'a`--) ]
   THEN GEN_TAC
   THEN REWRITE_TAC[o_THM,I_THM]
   THEN BETA_TAC
   THENL
     [  IMP_RES_THEN REWRITE_THM ONTO_INVERSE,
        ASM_REWRITE_TAC[SELECT_REFL]
     ]
  );

val o_EQ_INVERSE =
 store_thm
  ("o_EQ_INVERSE",
   (--`!(ss:'a->'b) (s1:'b->'c) s2.
      ONE_ONE ss /\ ONTO ss ==>
      ((s1 o ss = s2) = (s1 = s2 o (\y. @z. ss z = y)))`--),
   REPEAT STRIP_TAC
   THEN IMP_RES_TAC o_ONTO_11
   THEN EQ_TAC
   THENL [ DISCH_THEN (REWRITE_THM o SYM),
           DISCH_THEN REWRITE_THM ]
   THEN REWRITE_TAC[SYM(SPEC_ALL o_ASSOC)]
   THEN IMP_RES2_THEN REWRITE_THM o_INVERSE
   THEN REWRITE_TAC[I_o_ID]
  );

val o_ONTO =
 store_thm
  ("o_ONTO",
   (--`!(ss1:'b->'c) (ss2:'a->'b).
      ONTO ss1 /\ ONTO ss2 ==>
      ONTO (ss1 o ss2)`--),
   REWRITE_TAC[ONTO_THM]
   THEN REPEAT STRIP_TAC
   THEN UNDISCH_ALL_TAC
   THEN DISCH_THEN (STRIP_ASSUME_TAC o SPEC_ALL)
   THEN DISCH_THEN (STRIP_ASSUME_TAC o SPEC (--`x:'b`--))
   THEN EXISTS_TAC (--`x':'a`--)
   THEN ASM_REWRITE_TAC[o_THM]
  );

val o_ONE_ONE =
 store_thm
  ("o_ONE_ONE",
   (--`!(ss1:'b->'c) (ss2:'a->'b).
      ONE_ONE ss1 /\ ONE_ONE ss2 ==>
      ONE_ONE (ss1 o ss2)`--),
   REWRITE_TAC[ONE_ONE]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[o_THM]
  );


val biject_EQ_INVERSE =
 store_thm
  ("biject_EQ_INVERSE",
   (--`!y x (ss:'a->'b).
      ONE_ONE ss /\ ONTO ss ==>
      (((@z. ss z = y) = x) = (ss x = y))`--),
   REWRITE_TAC[ONE_ONE]
   THEN REPEAT STRIP_TAC
   THEN EQ_TAC
   THEN DISCH_THEN (REWRITE_THM o SYM)
   THENL
     [ IMP_RES_THEN REWRITE_THM ONTO_INVERSE,

       ASM_REWRITE_TAC[SELECT_REFL]
     ]
  );


val biject_EQ_INVERSE1 =
 store_thm
  ("biject_EQ_INVERSE1",
   (--`!y x (ss:'a->'b).
      ONE_ONE ss /\ ONTO ss ==>
      ((x = (@z. ss z = y)) = (ss x = y))`--),
   REWRITE_TAC[ONE_ONE]
   THEN REPEAT STRIP_TAC
   THEN EQ_TAC
   THENL
     [ DISCH_THEN REWRITE_THM
       THEN IMP_RES_THEN REWRITE_THM ONTO_INVERSE,

       DISCH_THEN (REWRITE_THM o SYM)
       THEN ASM_REWRITE_TAC[SELECT_REFL]
     ]
  );


val INVERSE_biject =
 store_thm
  ("INVERSE_biject",
   (--`!ss:'a->'b.
       ONE_ONE ss /\ ONTO ss ==>
       ONE_ONE (\y. @z. ss z = y) /\ ONTO (\y. @z. ss z = y)`--),
   REPEAT STRIP_TAC
   THENL
     [ REWRITE_TAC[ONE_ONE]
       THEN BETA_TAC
       THEN IMP_RES2_THEN REWRITE_THM biject_EQ_INVERSE1
       THEN IMP_RES_THEN REWRITE_THM ONTO_INVERSE,

       REWRITE_TAC[ONTO_THM]
       THEN GEN_TAC
       THEN BETA_TAC
       THEN IMP_RES2_THEN REWRITE_THM biject_EQ_INVERSE1
       THEN EXISTS_TAC (--`(ss:'a->'b) y`--)
       THEN ASM_REWRITE_TAC[]
     ]
  );


val IN_IDENT_subst =
 store_thm
  ("IN_IDENT_subst",
   (--`!s ss (z:'a).
      (!x. (x IN s) ==> (ss x = x)) /\ ONE_ONE ss ==>
      ((ss z IN s) = (z IN s))`--),
   REWRITE_TAC[ONE_ONE]
   THEN REPEAT STRIP_TAC
   THEN EQ_TAC
   THEN STRIP_TAC
   THEN RES_TAC
   THENL
     [  UNDISCH_LAST_TAC
        THEN ASM_REWRITE_TAC[]
        THEN DISCH_THEN REWRITE_ALL_THM
        THEN ASM_REWRITE_TAC[],

        ASM_REWRITE_TAC[]
     ]
  );


val MEMBER_IMP_POS_CARD = store_thm
   ("MEMBER_IMP_POS_CARD",
    (--`!s. FINITE s ==> !(x:'a). x IN s ==> (0 < CARD s)`--),
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC (DISJ_IMP (SPEC_ALL LESS_0_CASES))
    THEN PURE_ONCE_REWRITE_TAC[EQ_SYM_EQ]
    THEN IMP_RES_THEN ONCE_REWRITE_THM CARD_EQ_0
    THEN PURE_ONCE_REWRITE_TAC[SYM(SPEC_ALL MEMBER_NOT_EMPTY)]
    THEN EXISTS_TAC (--`x:'a`--)
    THEN ASM_REWRITE_TAC[]
   );


val SUB1_SUC = store_thm
   ("SUB1_SUC",
    (--`!m. (0 < m) ==> (SUC (m - 1) = m)`--),
    INDUCT_TAC
    THENL [REWRITE_TAC[NOT_LESS_0],
           REWRITE_TAC[LESS_0,SUC_SUB1]
          ]
   );


val UNION_INTER =
 store_thm
  ("UNION_INTER",
   (--`!s1 s2 s3 :'a->bool.
     (s1 UNION s2) INTER s3 =
     ((s1 INTER s3) UNION (s2 INTER s3))`--),
   ONCE_REWRITE_TAC[INTER_COMM]
   THEN REWRITE_TAC[UNION_OVER_INTER]
  );

val UNION_THM =
 store_thm
  ("UNION_THM",
   (--`!s t (x:'a).
      (EMPTY UNION t = t) /\
      (s UNION EMPTY = s) /\
      ((x INSERT s) UNION t = x INSERT (s UNION t)) /\
      (s UNION (x INSERT t) = x INSERT (s UNION t))`--),
   REWRITE_TAC[UNION_EMPTY,INSERT_UNION_EQ]
   THEN ONCE_REWRITE_TAC[UNION_COMM]
   THEN REWRITE_TAC[INSERT_UNION_EQ]
  );


val UNION_SUBSET =
 store_thm
  ("UNION_SUBSET",
   (--`!(s:'a->bool) t u.
     ((s UNION t) SUBSET u) = ((s SUBSET u) /\ (t SUBSET u))`--),
   REWRITE_TAC[SUBSET_DEF,IN_UNION]
   THEN REPEAT GEN_TAC
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
  );


val UNION_DIFF =
 store_thm
  ("UNION_DIFF",
   (--`!s t r:'a->bool. (s UNION t) DIFF r = ((s DIFF r) UNION (t DIFF r))`--),
   REWRITE_TAC[EXTENSION,IN_UNION,IN_DIFF]
   THEN REPEAT GEN_TAC
   THEN EQ_TAC
   THEN STRIP_TAC
   THEN ASM_REWRITE_TAC[]
  );

val SUBSET_DIFF =
 store_thm
  ("SUBSET_DIFF",
   (--`!s t r:'a->bool. (s SUBSET t) ==> (s DIFF r SUBSET t DIFF r)`--),
   REWRITE_TAC[SUBSET_DEF,IN_DIFF]
   THEN REPEAT GEN_TAC
   THEN DISCH_TAC
   THEN GEN_TAC
   THEN STRIP_TAC
   THEN RES_TAC
   THEN ASM_REWRITE_TAC[]
  );

val SUBSETS_UNION =
 store_thm
  ("SUBSETS_UNION",
    (--`!(s1:'a->bool) s2 t1 t2.
         s1 SUBSET t1 /\ s2 SUBSET t2 ==>
         (s1 UNION s2) SUBSET (t1 UNION t2)`--),
    REWRITE_TAC[SUBSET_DEF]
    THEN REWRITE_TAC[IN_UNION]
    THEN REPEAT STRIP_TAC (* 2 subgoals *)
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
   );


(* Theorems about DISJOINT: *)

val DISJOINT_INSERT2 = store_thm
   ("DISJOINT_INSERT2",
    (--`!s t (x:'a). DISJOINT s (x INSERT t) = (DISJOINT s t /\ ~(x IN s))`--),
    ONCE_REWRITE_TAC[DISJOINT_SYM]
    THEN REWRITE_TAC[DISJOINT_INSERT]
   );

val DISJOINT_UNION2 = store_thm
   ("DISJOINT_UNION2",
    (--`!s t r:'a->bool. DISJOINT s (t UNION r) = (DISJOINT s t /\ DISJOINT s r)`--),
    ONCE_REWRITE_TAC[DISJOINT_SYM]
    THEN REWRITE_TAC[DISJOINT_UNION]
   );

val DISJOINT_SUBSET =
 store_thm
  ("DISJOINT_SUBSET",
   (--`!s t r:'a->bool. s SUBSET t /\ DISJOINT t r ==> DISJOINT s r`--),
   REWRITE_TAC[SUBSET_DEF,IN_DISJOINT]
   THEN CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV)
   THEN REWRITE_TAC[DE_MORGAN_THM]
   THEN REPEAT STRIP_TAC
   THEN POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`x:'a`--))
   THENL
    [ FIRST_ASSUM (IMP_RES_TAC o CONTRAPOS o SPEC (--`x:'a`--))
      THEN ASM_REWRITE_TAC[],

      ASM_REWRITE_TAC[]
    ]
  );

val UNION_DELETE =
 store_thm
  ("UNION_DELETE",
   (--`!s t (e:'a).
        s UNION t DELETE e = (s DELETE e) UNION (t DELETE e)`--),
   REWRITE_TAC[EXTENSION]
   THEN REPEAT GEN_TAC
   THEN REWRITE_TAC[IN_UNION,IN_DELETE]
   THEN EQ_TAC
   THEN STRIP_TAC
   THEN ASM_REWRITE_TAC[]
  );


val IN = save_thm("IN", CONJ NOT_IN_EMPTY IN_INSERT);

val UNION = save_thm("UNION", CONJ UNION_EMPTY INSERT_UNION_EQ);

val INTER = save_thm("INTER", CONJ INTER_EMPTY INSERT_INTER);

val DELETE = save_thm("DELETE", CONJ EMPTY_DELETE DELETE_INSERT);

val SUBSET = save_thm("SUBSET", CONJ EMPTY_SUBSET INSERT_SUBSET);

val IMAGE = save_thm("IMAGE", CONJ IMAGE_EMPTY IMAGE_INSERT);

val DIFFF = save_thm("DIFFF", CONJ DIFF_EMPTY DIFF_INSERT);



(* ======================================================================== *)
(* UNION_SET is a function which takes a set of sets and produces the union *)
(* of all of them, that is, if S = {Si} then UNION_SET S = S1 U ... U Sn.   *)
(* ======================================================================== *)

val UNION_SET_EXISTS =
    TAC_PROOF
    (([], (--`!s:('a->bool)->bool.
                ?t. !x. x IN t = ?si. si IN s /\ x IN si`--)),
     GEN_TAC
     THEN EXISTS_TAC (--`\x:'a. ?si. si IN s /\ x IN si`--)
     THEN REWRITE_TAC[SPECIFICATION]
     THEN BETA_TAC
     THEN REWRITE_TAC[]
    );


local
open Rsyntax
in
val IN_UNION_SET =
    let val th1 = CONV_RULE SKOLEM_CONV UNION_SET_EXISTS in
    new_specification{name="IN_UNION_SET",
                      consts=[{const_name="UNION_SET",fixity=NONE}],
                      sat_thm=th1}
    end
end;


val UNION_SET_EMPTY_LEMMA = TAC_PROOF
   (([], (--`UNION_SET EMPTY = (EMPTY:'a->bool)`--)),
    REWRITE_TAC [EXTENSION, IN_UNION_SET, IN]
   );

val UNION_SET_INSERT_LEMMA = TAC_PROOF
    (([],  (--`! (si:'a->bool) (s:('a->bool)->bool) .
            UNION_SET (si INSERT s) = si UNION (UNION_SET s)`--)),
    REWRITE_TAC [EXTENSION, IN_UNION_SET, IN_UNION, IN]
    THEN REPEAT GEN_TAC
    THEN EQ_TAC
    THEN ONCE_REWRITE_TAC[EQ_SYM_EQ]
    THEN REPEAT STRIP_TAC
    THENL [ ALL_TAC,

            DISJ2_TAC
            THEN EXISTS_TAC (--`si':'a->bool`--),

            EXISTS_TAC (--`si:'a->bool`--),

            EXISTS_TAC (--`si':'a->bool`--)
          ]
    THEN ASM_REWRITE_TAC []
    );


val UNION_SET = save_thm ("UNION_SET",
                          CONJ UNION_SET_EMPTY_LEMMA UNION_SET_INSERT_LEMMA);


val UNION_SET_UNION =
 store_thm
  ("UNION_SET_UNION",
   (--`!s t : ('a->bool)->bool.
      UNION_SET (s UNION t) =
                     UNION_SET s UNION UNION_SET t`--),
   REWRITE_TAC[EXTENSION,IN_UNION,IN_UNION_SET]
   THEN REPEAT GEN_TAC
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THENL [ DISJ1_TAC, DISJ2_TAC, ALL_TAC, ALL_TAC ]
   THEN EXISTS_TAC (--`si:'a->bool`--)
   THEN ASM_REWRITE_TAC[]
  );


val EMPTY_UNION_SET =
 store_thm
  ("EMPTY_UNION_SET",
   (--`!s. (UNION_SET s = {}) = (!si:'a->bool. si IN s ==> (si = {}))`--),
   REWRITE_TAC[EXTENSION,IN,IN_UNION_SET]
   THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
   THEN REWRITE_TAC[DE_MORGAN_THM,(SYM o SPEC_ALL)IMP_DISJ_THM]
   THEN CONV_TAC (DEPTH_CONV RIGHT_IMP_FORALL_CONV)
   THEN GEN_TAC
   THEN EQ_TAC
   THEN DISCH_THEN REWRITE_THM
  );


val UNION_SET_EMPTY =
 store_thm
  ("UNION_SET_EMPTY",
   (--`!s:('a->bool)->bool. (UNION_SET s = {}) = ((s = {}) \/ (s = {{}}))`--),
   GEN_TAC
   THEN ASM_CASES_TAC (--`s = ({}:('a->bool)->bool)`--)
   THEN ASM_REWRITE_TAC[UNION_SET]
   THEN UNDISCH_ALL_TAC
   THEN REWRITE_TAC[EXTENSION]
   THEN REWRITE_TAC[IN,IN_UNION_SET]
   THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
   THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
   THEN REWRITE_TAC[DE_MORGAN_THM]
   THEN STRIP_TAC
   THEN CONV_TAC (ONCE_DEPTH_CONV FORALL_SYM_CONV)
   THEN REWRITE_TAC[(SYM o SPEC_ALL)IMP_DISJ_THM]
   THEN CONV_TAC (DEPTH_CONV FORALL_IMP_CONV)
   THEN EQ_TAC
   THENL
      [ DISCH_TAC
        THEN GEN_TAC
        THEN EQ_TAC
        THENL
          [ ASM_REWRITE_TAC[EXTENSION,IN],

            DISCH_THEN REWRITE_THM
            THEN RES_TAC
            THEN ASM_CASES_TAC (--`x = ({}:'a->bool)`--)
            THENL
               [ POP_ASSUM (ASM_REWRITE_THM o SYM),

                 POP_ASSUM MP_TAC
                 THEN REWRITE_TAC[(SYM o SPEC_ALL)MEMBER_NOT_EMPTY]
                 THEN ASM_REWRITE_TAC[]
               ]
          ],

        DISCH_THEN REWRITE_THM
        THEN GEN_TAC
        THEN DISCH_THEN REWRITE_THM
        THEN REWRITE_TAC[IN]
      ]
  );


val UNION_SET_EMPTY_INSERT =
 store_thm
  ("UNION_SET_EMPTY_INSERT",
   (--`!s:('a->bool)->bool. UNION_SET ({} INSERT s) = UNION_SET s`--),
   REWRITE_TAC[UNION_SET,UNION_EMPTY]
  );

val UNION_SET_DELETE =
 store_thm
  ("UNION_SET_DELETE",
   (--`!(s:('a->bool)->bool) e.
        UNION_SET {si DELETE e | si IN s} = (UNION_SET s) DELETE e`--),
   REWRITE_TAC[EXTENSION]
   THEN REWRITE_TAC[IN_UNION_SET,IN_DELETE,GSPECIFICATION]
   THEN BETA_TAC
   THEN REWRITE_TAC[PAIR_EQ]
   THEN REPEAT GEN_TAC
   THEN EQ_TAC
   THENL
      [ STRIP_TAC
        THEN CONJ_TAC
        THENL [ EXISTS_TAC (--`x':'a->bool`--), ALL_TAC ]
        THEN POP_ASSUM MP_TAC
        THEN ASM_REWRITE_TAC[IN_DELETE]
        THEN DISCH_THEN REWRITE_THM,

        STRIP_TAC
        THEN EXISTS_TAC (--`si DELETE (e:'a)`--)
        THEN ASM_REWRITE_TAC[IN_DELETE]
        THEN EXISTS_TAC (--`si:'a->bool`--)
        THEN ASM_REWRITE_TAC[]
      ]
  );


val FINITE_UNION_SET_IMP_LEMMA =
 TAC_PROOF
  (([], (--`!s. FINITE s ==> (!si:'a->bool. si IN s ==> FINITE si) ==>
                FINITE (UNION_SET s)`--)),
   SET_INDUCT_TAC
   THEN REWRITE_TAC[IN,UNION_SET,FINITE_EMPTY,FINITE_UNION]
   THEN REPEAT STRIP_TAC
   THENL
     [ FIRST_ASSUM MATCH_MP_TAC
       THEN REWRITE_TAC[],

       FIRST_ASSUM (MATCH_MP_TAC o (test (dest_imp o concl)))
       THEN REPEAT STRIP_TAC
       THEN FIRST_ASSUM MATCH_MP_TAC
       THEN ASM_REWRITE_TAC[]
     ]
  );


val FINITE_UNION_SET_IMP =
 store_thm
  ("FINITE_UNION_SET_IMP",
   (--`!s. FINITE s /\ (!si:'a->bool. si IN s ==> FINITE si) ==>
           FINITE (UNION_SET s)`--),
   REPEAT STRIP_TAC
   THEN IMP_RES_TAC FINITE_UNION_SET_IMP_LEMMA
  );


val FINITE_UNION_SET_LEMMA1 =
 TAC_PROOF
  (([], (--`!s. FINITE (UNION_SET s) ==>
                (!si:'a->bool. si IN s ==> FINITE si)`--)),
   GEN_TAC
   THEN CONV_TAC CONTRAPOS_CONV
   THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
   THEN REWRITE_TAC[NOT_IMP]
   THEN STRIP_TAC
   THEN UNDISCH_ALL_TAC
   THEN ONCE_REWRITE_TAC[DECOMPOSITION]
   THEN STRIP_TAC
   THEN STRIP_TAC
   THEN ASM_REWRITE_TAC[UNION_SET,FINITE_UNION]
  );


val FINITE_UNION_SET =
 store_thm
  ("FINITE_UNION_SET",
   (--`!(s:('a->bool)->bool). FINITE s ==>
        (FINITE (UNION_SET s) = (!si. si IN s ==> FINITE si))`--),
   GEN_TAC
   THEN STRIP_TAC
   THEN EQ_TAC
   THENL
     [ REWRITE_TAC[FINITE_UNION_SET_LEMMA1],

       IMP_RES_TAC FINITE_UNION_SET_IMP_LEMMA
     ]
  );


val GSPEC_EMPTY_LEMMA =
 TAC_PROOF
  (([], (--`!s (e:'a). ({si DELETE e | si IN s} = {}) = (s = {})`--)),
   REPEAT GEN_TAC
   THEN EQ_TAC
   THENL
      [ CONV_TAC (RATOR_CONV (RAND_CONV (REWRITE_CONV[EXTENSION])))
        THEN REWRITE_TAC[IN]
        THEN REWRITE_TAC[GSPECIFICATION]
        THEN BETA_TAC
        THEN REWRITE_TAC[PAIR_EQ]
        THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
        THEN REWRITE_TAC[DE_MORGAN_THM]
        THEN ONCE_REWRITE_TAC[DISJ_SYM]
        THEN CONV_TAC (ONCE_DEPTH_CONV FORALL_SYM_CONV)
        THEN CONV_TAC (DEPTH_CONV FORALL_OR_CONV)
        THEN CONV_TAC (DEPTH_CONV FORALL_NOT_CONV)
        THEN SUBGOAL_THEN (--`!y. ?x. x = y DELETE (e:'a)`--) REWRITE_THM
        THENL
           [ GEN_TAC
             THEN EXISTS_TAC (--`y DELETE (e:'a)`--)
             THEN REFL_TAC,

             CONV_TAC (DEPTH_CONV FORALL_NOT_CONV)
             THEN REWRITE_TAC[MEMBER_NOT_EMPTY]
           ],

        DISCH_THEN REWRITE_THM
        THEN REWRITE_TAC[EXTENSION]
        THEN REWRITE_TAC[IN]
        THEN REWRITE_TAC[GSPECIFICATION]
        THEN BETA_TAC
        THEN REWRITE_TAC[PAIR_EQ]
      ]
  );


val _ = export_theory();

val _ = print_theory_to_file "-" "more_set.lst";

val _ = html_theory "more_set";

