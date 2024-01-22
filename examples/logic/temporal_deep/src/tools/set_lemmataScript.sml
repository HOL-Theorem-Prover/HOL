open HolKernel Parse boolLib bossLib

(*
quietdec := true;
map load ["pred_setTheory"];
*)

open pred_setTheory;
open Sanity;

val _ = hide "S";
val _ = hide "I";

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)


val _ = new_theory "set_lemmata";
val _ = ParseExtras.temp_loose_equality()


val DIFF_OVER_INTER =
 store_thm
  ("DIFF_OVER_INTER",
   ``(!S1 S2 S3. (S1 INTER (S2 DIFF S3) = (S1 INTER S2) DIFF S3)) /\
     (!S1 S2 S3. ((S2 DIFF S3) INTER S1 = (S1 INTER S2) DIFF S3))``,

   SIMP_TAC std_ss [INTER_DEF, DIFF_DEF, EXTENSION, GSPECIFICATION] THEN
   PROVE_TAC[]);


val INTER_OVER_DIFF =
  store_thm
   ("INTER_OVER_DIFF",
    ``(!S1 S2 S3. (S1 DIFF (S2 INTER S3) = (S1 DIFF S2) UNION (S1 DIFF S3))) /\
      (!S1 S2 S3. ((S1 INTER S2) DIFF S3 = (S1 DIFF S3) INTER (S2 DIFF S3)))``,

    REWRITE_TAC [SUBSET_DEF,IN_DIFF,IN_INTER,IN_UNION,DIFF_DEF,EXTENSION,GSPECIFICATION] THEN PROVE_TAC []);


val UNION_OVER_DIFF =
  store_thm
   ("UNION_OVER_DIFF",
    ``(!S1 S2 S3. (S1 DIFF (S2 UNION S3) = (S1 DIFF S2) INTER (S1 DIFF S3))) /\
      (!S1 S2 S3. (((S1 UNION S2) DIFF S3) = ((S1 DIFF S3) UNION (S2 DIFF S3))))``,

    REWRITE_TAC [SUBSET_DEF,IN_DIFF,IN_INTER,IN_UNION,DIFF_DEF,EXTENSION,GSPECIFICATION] THEN PROVE_TAC []);


val BIGUNION_OVER_DIFF =
  store_thm
   ("BIGUNION_OVER_DIFF",
    ``!P. (UNIV DIFF (BIGUNION {s | ?(n:num). s = (P n)})) = (BIGINTER {s | ?(n:num). (s = (UNIV DIFF (P n)))})``,


      SIMP_TAC std_ss [DIFF_DEF, BIGUNION, BIGINTER, GSPECIFICATION, IMP_DISJ_THM, IN_UNIV] THEN
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
      PROVE_TAC[IN_COMPL]);


val BIGINTER_OVER_DIFF =
  store_thm
   ("BIGINTER_OVER_DIFF",
    ``!P. (UNIV DIFF (BIGINTER {s | ?(n:num). s = (P n)})) = (BIGUNION {s | ?(n:num). (s = (UNIV DIFF (P n)))})``,


      SIMP_TAC std_ss [DIFF_DEF, BIGUNION, BIGINTER, GSPECIFICATION, IMP_DISJ_THM, IN_UNIV] THEN
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
      PROVE_TAC[IN_COMPL]);


val COMPL_11 = store_thm
  ("COMPL_11",
  ``!s t. (COMPL s = COMPL t) = (s = t)``,
  SIMP_TAC std_ss [IN_COMPL,EXTENSION]);


val COMPL_SUBSET = store_thm
  ("COMPL_SUBSET",
  ``!s t. (COMPL s SUBSET COMPL t) = (t SUBSET s)``,
  SIMP_TAC std_ss [IN_COMPL,SUBSET_DEF] THEN PROVE_TAC[]);


val UNION_INSERT =
 store_thm
  ("UNION_INSERT",
   ``!S1 S2 a. (S1 UNION (a INSERT S2)) = ((a INSERT S1) UNION S2)``,

SIMP_TAC std_ss [UNION_DEF, INSERT_DEF, EXTENSION, GSPECIFICATION] THEN
PROVE_TAC[]);


val UNION_INTER_ABSORPTION =
 store_thm
  ("UNION_INTER_ABSORPTION",
   ``!s1 s2. (((s1 UNION s2) INTER s1) = s1) /\ ((s1 UNION (s2 INTER s1)) = s1)``,

   REPEAT STRIP_TAC THEN
   REWRITE_TAC [UNION_DEF, INTER_DEF, EXTENSION, GSPECIFICATION] THEN
   FULL_SIMP_TAC arith_ss [] THEN
   PROVE_TAC[]);


val INTER_INTER_ABSORPTION =
 store_thm
  ("INTER_INTER_ABSORPTION",
    ``!S a. S INTER a INTER a = S INTER a``,

       PROVE_TAC[INTER_SUBSET, SUBSET_INTER_ABSORPTION]
);

val SUBSET_COMPL_DISJOINT =
 store_thm
  ("SUBSET_COMPL_DISJOINT",
   ``!s1 s2. (s1 SUBSET (COMPL s2)) = (DISJOINT s1 s2)``,

   SIMP_TAC arith_ss [SUBSET_DEF, COMPL_DEF, DISJOINT_DEF, INTER_DEF, DIFF_DEF, IN_UNIV, GSPECIFICATION, EXTENSION, NOT_IN_EMPTY] THEN
   PROVE_TAC[]
);


val DIFF_SUBSET_ELIM =
 store_thm
  ("DIFF_SUBSET_ELIM",
   ``!S1 S2 S. (((S1 DIFF S2) SUBSET S) = (S1 SUBSET (S UNION S2))) /\
               ((S SUBSET (S1 DIFF S2)) = ((S SUBSET S1) /\ (DISJOINT S S2)))``,

   SIMP_TAC arith_ss [DIFF_DEF, SUBSET_DEF, UNION_DEF, GSPECIFICATION, DISJOINT_DEF, INTER_DEF,
                      NOT_IN_EMPTY, EXTENSION] THEN
   PROVE_TAC[]);


val UNION_SING =
 store_thm
  ("UNION_SING",
   ``!S s. (S UNION {s} = s INSERT S) /\ ({s} UNION S = s INSERT S)``,

   SIMP_TAC arith_ss [UNION_DEF, INSERT_DEF, GSPECIFICATION, EXTENSION, NOT_IN_EMPTY] THEN
   PROVE_TAC[]);


val COMPL_CLAUSES_COMM =
 store_thm
  ("COMPL_CLAUSES_COMM",
   ``!s. (s INTER COMPL s = {}) /\ (s UNION COMPL s = UNIV)``,

   METIS_TAC[COMPL_CLAUSES, UNION_COMM, INTER_COMM]);


val INTER_COMPL_DIFF =
 store_thm
  ("INTER_COMPL_DIFF",
   ``!S1 S2. (S1 INTER COMPL S2 = S1 DIFF S2)``,

   SIMP_TAC arith_ss [DIFF_DEF, INTER_DEF, COMPL_DEF, GSPECIFICATION, EXTENSION, IN_UNIV]);



val COMPL_OVER_UNION =
 store_thm
  ("COMPL_OVER_UNION",
   ``!S1 S2. (((COMPL S1) UNION S2) = COMPL(S1 INTER COMPL S2)) /\
             ((S2 UNION (COMPL S1)) = COMPL(COMPL S2 INTER S1))``,

   SIMP_TAC arith_ss [INTER_DEF, UNION_DEF, GSPECIFICATION, EXTENSION, IN_UNIV, IN_COMPL]);


val DIFF_SUBSET_EMPTY =
 store_thm
  ("DIFF_SUBSET_EMPTY",
   ``!S1 S2. (S1 DIFF S2 = EMPTY) = (S1 SUBSET S2)``,

   SIMP_TAC arith_ss [DIFF_DEF, SUBSET_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION] THEN
   PROVE_TAC[]);



val INTER_DIFF_EMPTY =
 store_thm
  ("INTER_DIFF_EMPTY",
   ``(!S1 S2. (S1 INTER S2) DIFF S1 = EMPTY) /\ (!S1 S2. (S1 INTER S2) DIFF S2 = EMPTY)``,

   SIMP_TAC std_ss [INTER_DEF, DIFF_DEF, EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] THEN
   PROVE_TAC[]);


val DISJOINT_DIFF_ELIM =
 store_thm
  ("DISJOINT_DIFF_ELIM",
   ``!S1 S2. DISJOINT S1 (S2 DIFF S1) /\ DISJOINT (S2 DIFF S1) S1``,

   SIMP_TAC arith_ss [DISJOINT_DEF, DIFF_DEF, INTER_DEF, EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] THEN
   PROVE_TAC[]);


val DISJOINT_DIFF_ELIM_SYM =
 store_thm
  ("DISJOINT_DIFF_ELIM_SYM",
   ``!S1 S2 S3. (DISJOINT S1 S3 \/ DISJOINT S3 S1) ==>
      ((DISJOINT S1 (S2 DIFF S3) = DISJOINT S1 S2) /\
       (DISJOINT (S2 DIFF S3) S1 = DISJOINT S2 S1))``,

   SIMP_TAC arith_ss [DISJOINT_DEF, DIFF_DEF, INTER_DEF, EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] THEN
   PROVE_TAC[]);


val DISJOINT_INSERT_SYM =
 store_thm
  ("DISJOINT_INSERT_SYM",
   ``!s S1 S2. DISJOINT S1 (s INSERT S2) = ((DISJOINT S1 S2) /\ ~(s IN S1))``,

   PROVE_TAC[DISJOINT_INSERT, DISJOINT_SYM]);


val DISJOINT_DIFF_SYM =
 store_thm
  ("DISJOINT_DIFF_SYM",
   ``!S1 S2 S3. DISJOINT S1 (S2 DIFF S3) = DISJOINT (S1 DIFF S3) S2``,

   SIMP_TAC arith_ss [DISJOINT_DEF, DIFF_DEF, INTER_DEF, EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] THEN
   PROVE_TAC[]);


val DISJOINT_DISJ_THM =
  store_thm ("DISJOINT_DISJ_THM",
    ``!S1 S2.
        DISJOINT S1 S2 = !x. ~(x IN S1) \/ ~(x IN S2)``,

SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL] THEN
PROVE_TAC[]);


val DIFF_DISJOINT =
 store_thm
  ("DIFF_DISJOINT",
   ``!S1 S2. (S1 DIFF S2 = S1) = DISJOINT S1 S2``,

   SIMP_TAC arith_ss [DISJOINT_DEF, DIFF_DEF, INTER_DEF, EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] THEN
   PROVE_TAC[]);


val DIFF_UNION_ELIM =
 store_thm
  ("DIFF_UNION_ELIM",
   ``!S1 S2. (((S1 DIFF S2) UNION S2) = (S1 UNION S2)) /\
             ((S2 UNION (S1 DIFF S2)) = (S2 UNION S1))``,

      SIMP_TAC std_ss [UNION_DEF, DIFF_DEF, EXTENSION, GSPECIFICATION] THEN
      METIS_TAC[]);


val IMAGE_DIFF =
 store_thm
  ("IMAGE_DIFF",

   ``!f S1 S2. (INJ f (S1 UNION S2) UNIV) ==> ((IMAGE f (S1 DIFF S2)) = ((IMAGE f S1) DIFF (IMAGE f S2)))``,

   SIMP_TAC std_ss [INJ_DEF,
                  IN_UNION,
                  IN_UNIV,
                  IMAGE_DEF,
                  DIFF_DEF,
                  EXTENSION,
                  GSPECIFICATION] THEN
   METIS_TAC[]);


val IMAGE_ID_SUBSET =
 store_thm
  ("IMAGE_ID_SUBSET",

   ``!f S. (!x. (x IN S) ==> (f x = x)) ==> (IMAGE f S = S)``,

   REPEAT STRIP_TAC THEN
   SIMP_TAC std_ss [IMAGE_DEF, EXTENSION, GSPECIFICATION] THEN
   METIS_TAC[]);

val INJ_SUBSET_DOMAIN =
 store_thm
  ("INJ_SUBSET_DOMAIN",
   ``!f S1 S2 S. (S2 SUBSET S1) ==> (INJ f S1 S) ==> (INJ f S2 S)``,

   REWRITE_TAC[INJ_DEF, SUBSET_DEF] THEN
   PROVE_TAC[]);


val INJ_INVERSE =
 store_thm
  ("INJ_INVERSE",

  ``!S1 S2 f. INJ f S1 S2 ==> (?g. !x. (x IN S1) ==> (g(f(x)) = x))``,

  REPEAT STRIP_TAC THEN
  EXISTS_TAC ``\S:'b. (@x:'a. ((x IN S1 /\ ((f x) = S))))`` THEN
  REPEAT STRIP_TAC THEN
  SIMP_TAC std_ss [] THEN
  `!x'. (x' IN S1 /\ (f x' = f x)) = (x' = x)` by METIS_TAC[INJ_DEF] THEN
  ASM_SIMP_TAC std_ss []
);


val INSERT_SING =
 store_thm
  ("INSERT_SING",
    ``!x t s. (x INSERT t = {s}) = ((x = s) /\ ((t = {}) \/ (t = {s})))``,
    SIMP_TAC std_ss [INSERT_DEF, NOT_IN_EMPTY, EXTENSION, GSPECIFICATION] THEN
    PROVE_TAC[]
    );



val DIFF_DIFF_INTER =
 store_thm
  ("DIFF_DIFF_INTER",
    ``!A B. (A DIFF (A DIFF B)) = (A INTER B)``,

    SIMP_TAC std_ss [DIFF_DEF, INTER_DEF, EXTENSION, GSPECIFICATION] THEN
    PROVE_TAC[]);

val INJECTIVE_IMAGE_EQ =
  store_thm ("INJECTIVE_IMAGE_EQ",
    ``!f s1 s2. (!x y.  ((x IN (s1 UNION s2) /\ y IN (s1 UNION s2)) ==>
          ((f x = f y) ==> (x = y)))) ==>
          ((IMAGE f s1 = IMAGE f s2) = (s1 = s2))``,

    REPEAT STRIP_TAC THEN EQ_TAC THENL [
      ALL_TAC,
      SIMP_TAC std_ss []
    ] THEN
    FULL_SIMP_TAC std_ss [EXTENSION, IN_IMAGE, IN_UNION] THEN
    METIS_TAC[]);


val SUBSET_IMAGE___ORGINAL_EXISTS =
  store_thm ("SUBSET_IMAGE___ORGINAL_EXISTS",
  ``!f os fs. (fs SUBSET (IMAGE f os)) ==>
          (?s. s SUBSET os /\ (fs = IMAGE f s))``,

  REPEAT STRIP_TAC THEN
  Q_TAC EXISTS_TAC `os INTER (\x. (f x) IN fs)` THEN
  REWRITE_TAC[INTER_SUBSET] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, EXTENSION, IN_INTER,
    prove (``x IN (\x. P x) = P x``, SIMP_TAC std_ss [IN_DEF]) ] THEN
  METIS_TAC[]);



val DISJOINT_SUBSET_BOTH =
  store_thm ("DISJOINT_SUBSET_BOTH",
    ``!s t s' t'. (s SUBSET s' /\ t SUBSET t' /\ DISJOINT s' t') ==>
                   DISJOINT s t``,

   SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, SUBSET_DEF, NOT_IN_EMPTY,
    IN_INTER] THEN
   PROVE_TAC[]);


val FINITE_POW_IFF = store_thm
  ("FINITE_POW_IFF",
   ``!s. FINITE (POW s) = FINITE s``,
   METIS_TAC[finite_countable, infinite_pow_uncountable, FINITE_POW]);


val SUBSET_POW_IFF =
  store_thm ("SUBSET_POW_IFF",
    ``!s t. (POW s SUBSET POW t) = s SUBSET t``,

   SIMP_TAC std_ss [SUBSET_DEF, IN_POW] THEN
   PROVE_TAC[]);


val _ = export_theory();
