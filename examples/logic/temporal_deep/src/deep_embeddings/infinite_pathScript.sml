open HolKernel Parse boolLib bossLib;

(*
quietdec := true;

val home_dir = (concat Globals.HOLDIR "/examples/temporal_deep/");
loadPath := (concat home_dir "src/deep_embeddings") ::
            (concat home_dir "src/tools") :: !loadPath;

map load
 ["pred_setTheory", "pairTheory", "arithmeticTheory", "tuerk_tacticsLib",
  "containerTheory", "listTheory", "prop_logicTheory"];
*)


open pred_setTheory pairTheory arithmeticTheory tuerk_tacticsLib
     containerTheory listTheory prop_logicTheory;
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



val _ = new_theory "infinite_path";
val _ = ParseExtras.temp_loose_equality()


(******************************************************************************
* Elementary functions and predicates on temporal_paths
******************************************************************************)
val EMPTY_PATH_def =
 Define
   `EMPTY_PATH = (\n:num. EMPTY)`;


val PATH_TAIL_def =
 Define
   `PATH_TAIL t v = (\n:num. v (n+t))`;


val PATH_MAP_def =
 Define
   `(PATH_MAP (f: num -> 'a -> 'b) v) = (\n:num. (f n (v n)))`;


val PATH_RESTRICT_def =
 Define
   `PATH_RESTRICT v r = PATH_MAP (\n s. (s INTER r)) v`;


val PATH_RESTN_def =
 Define
   `(PATH_RESTN v (n:num)) = (\t:num. v (t+n))`;


val PATH_REST_def =
 Define
   `(PATH_REST v) = (PATH_RESTN v 1)`;


val PATH_UNION_def =
 Define
   `PATH_UNION v w = (\n:num. ((v n) UNION (w n)))`;


val PATH_DIFF_def =
 Define
   `PATH_DIFF v w = (\n:num. ((v n) DIFF w))`;


val PATH_SUBSET_def =
 Define
   `(PATH_SUBSET v (w:'a set)) = (!n:num. ((v n) SUBSET w))`;


val PATH_VAR_RENAMING_def =
 Define
   `(PATH_VAR_RENAMING (f:'a->'b) v) =
       (PATH_MAP (\n:num. \s. IMAGE f s) v)`;


val PATH_USED_VARS_def =
 Define
   `(PATH_USED_VARS w = BIGUNION {w n | n >= 0})`;


val IMP_ON_PATH_RESTN_def =
 Define
   `IMP_ON_PATH_RESTN (k:num) v a b = !t:num. (t >= k) ==> ((P_SEM (v t) a) ==> (P_SEM (v t) b))`;


val EQUIV_ON_PATH_RESTN_def =
 Define
   `EQUIV_ON_PATH_RESTN (k:num) v a b = !t:num. (t >= k) ==> ((P_SEM (v t) a) = (P_SEM (v t) b))`;


val NAND_ON_PATH_RESTN_def =
 Define
   `NAND_ON_PATH_RESTN (k:num) v a b = !t:num. (t >= k) ==> (~(P_SEM (v t) a) \/ ~(P_SEM (v t) b))`;


val BEFORE_ON_PATH_RESTN_def =
 Define
   `BEFORE_ON_PATH_RESTN (t:num) v a b = !t':num. (t <= t' /\ (P_SEM (v t') b)) ==> (?u:num. t <= u /\ u <= t' /\ P_SEM (v u) a)`;


val BEFORE_ON_PATH_RESTN_STRONG_def =
 Define
   `BEFORE_ON_PATH_RESTN_STRONG (t:num) v a b = !t':num. (t <= t' /\ (P_SEM (v t') b)) ==> (?u:num. t <= u /\ u < t' /\ P_SEM (v u) a)`;


val NOT_ON_PATH_RESTN_def =
 Define
   `NOT_ON_PATH_RESTN (t:num) v a = !t':num. (t <= t') ==> ~P_SEM (v t') a`;


val IS_ON_PATH_RESTN_def =
 Define
   `IS_ON_PATH_RESTN (t:num) v a = ~(NOT_ON_PATH_RESTN t v a)`;


val EQUIV_PATH_RESTN_def =
  Define `EQUIV_PATH_RESTN (t:num) v1 v2 =
      ((!l:num. t <= l ==> ((v1 l) = (v2 l))))`;


val PATH_EXTENSION_def =
 Define
   `(PATH_EXTENSION w (q:'a) (P:num->bool)) =
      (\n:num. (if (P n) then (q INSERT w n) else (w n)))`;

val CHOOSEN_PATH_def =
Define
    `(CHOOSEN_PATH S0 S 0 = @x. x IN S0) /\
      (CHOOSEN_PATH S0 S (SUC n) = @x. x IN (S (CHOOSEN_PATH S0 S n) (SUC n)))`;

val INF_ELEMENTS_OF_PATH_def =
Define
`INF_ELEMENTS_OF_PATH w = {s | !n. ?m. m > n /\ (w m = s)}`;

val ELEMENTS_OF_PATH_def =
Define
`ELEMENTS_OF_PATH w = {s | ?m:num. (w m = s)}`;


(******************************************************************************
* Lemmata about paths
******************************************************************************)

val PATH_USED_VARS_THM =
 store_thm
  ("PATH_USED_VARS_THM",
   ``!w x. (?n. x IN w n) = (x IN PATH_USED_VARS w)``,

   SIMP_TAC arith_ss [PATH_USED_VARS_def, IN_BIGUNION, GSPECIFICATION, EXISTS_PROD] THEN
   METIS_TAC[])


val PATH_DIFF_EMPTY =
 store_thm
  ("PATH_DIFF_EMPTY",
   ``!v. PATH_DIFF v EMPTY = v``,

   REWRITE_TAC[PATH_DIFF_def, PATH_MAP_def, DIFF_DEF, NOT_IN_EMPTY] THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   SIMP_TAC arith_ss [EXTENSION, GSPECIFICATION]);


val PATH_DIFF_PATH_RESTRICT =
 store_thm
  ("PATH_DIFF_PATH_RESTRICT",
   ``!v S. (PATH_DIFF v (COMPL S) = PATH_RESTRICT v S) /\
           (PATH_RESTRICT v (COMPL S) = PATH_DIFF v S)``,

   REWRITE_TAC[PATH_DIFF_def, INTER_DEF, PATH_RESTRICT_def, PATH_MAP_def, DIFF_DEF, NOT_IN_EMPTY, IN_COMPL] THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   SIMP_TAC arith_ss [EXTENSION, GSPECIFICATION]);


val PATH_UNION_COMM =
 store_thm
  ("PATH_UNION_COMM",
   ``!v w. PATH_UNION v w = PATH_UNION w v``,

   REWRITE_TAC[PATH_UNION_def] THEN
   PROVE_TAC [UNION_COMM]);


val PATH_UNION_ASSOC =
 store_thm
  ("PATH_UNION_ASSOC",
   ``!s t u. PATH_UNION s (PATH_UNION t u) = PATH_UNION (PATH_UNION s t) u``,

   REWRITE_TAC[PATH_UNION_def] THEN
   PROVE_TAC [UNION_ASSOC]);


val PATH_UNION_EMPTY_PATH =
 store_thm
  ("PATH_UNION_EMPTY_PATH",
   ``!v. (PATH_UNION v EMPTY_PATH = v) /\ (PATH_UNION EMPTY_PATH v = v)``,

   REWRITE_TAC[PATH_UNION_def, EMPTY_PATH_def, UNION_EMPTY] THEN
   METIS_TAC []);


val PATH_RESTRICT_SUBSET =
 store_thm
  ("PATH_RESTRICT_SUBSET",
   ``!v w S. (v = PATH_RESTRICT w S) ==> (!n. (v n) SUBSET S)``,

   SIMP_TAC arith_ss [PATH_RESTRICT_def, PATH_MAP_def, SUBSET_DEF, INTER_DEF, GSPECIFICATION]);


val PATH_RESTRICT_PATH_SUBSET =
 store_thm
  ("PATH_RESTRICT_PATH_SUBSET",
    ``!w S. (PATH_RESTRICT w S = w) = PATH_SUBSET w S``,

    SIMP_TAC std_ss [PATH_SUBSET_def, PATH_RESTRICT_def, PATH_MAP_def, SUBSET_DEF] THEN
    ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
    ASM_SIMP_TAC std_ss [EXTENSION, IN_INTER] THEN
    PROVE_TAC[]
  );


val PATH_SUBSET_PATH_DIFF =
 store_thm
  ("PATH_SUBSET_PATH_DIFF",
  ``!w S1 S2. PATH_SUBSET (PATH_DIFF w S1) S2 = PATH_SUBSET w (S2 UNION S1)``,

  SIMP_TAC std_ss [PATH_SUBSET_def, PATH_DIFF_def, SUBSET_DEF, IN_DIFF, IN_UNION] THEN
  METIS_TAC[]);


val PATH_PARTITION =
 store_thm
  ("PATH_PARTITION",

  ``!w S1 S2. (PATH_SUBSET w (S1 UNION S2)) ==> (w = PATH_UNION (PATH_RESTRICT w S1) (PATH_RESTRICT w S2))``,

   SIMP_TAC std_ss [PATH_UNION_def,
                    PATH_MAP_def,
                    PATH_RESTRICT_def,
                    INTER_DEF,
                    UNION_DEF,
                    PATH_SUBSET_def,
                    SUBSET_DEF] THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   SIMP_TAC arith_ss [EXTENSION, GSPECIFICATION] THEN
   REPEAT STRIP_TAC THEN
   METIS_TAC []
)


val PATH_VAR_RENAMING_11 =
 store_thm
  ("PATH_VAR_RENAMING_11",

   ``!f S x y. (PATH_SUBSET x S /\ PATH_SUBSET y S /\ INJ f S UNIV) ==>
               ((PATH_VAR_RENAMING f x = PATH_VAR_RENAMING f y) = (x = y))``,

     SIMP_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, INJ_DEF, PATH_VAR_RENAMING_def, IN_UNIV,
                      PATH_MAP_def, IMAGE_DEF] THEN
     REPEAT STRIP_TAC THEN
     ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
     METIS_TAC[]);


val PATH_SUBSET_UNIV =
 store_thm
  ("PATH_SUBSET_UNIV",

   ``!w. PATH_SUBSET w UNIV``,

   REWRITE_TAC [PATH_SUBSET_def, SUBSET_UNIV]);


val PATH_RESTN_PATH_RESTN_ELIM =
 store_thm
  ("PATH_RESTN_PATH_RESTN_ELIM",
   ``!v n1 n2. (PATH_RESTN (PATH_RESTN v n1) n2) = PATH_RESTN v (n1+n2)``,

   SIMP_TAC arith_ss [PATH_RESTN_def]);


val IMP_ON_PATH_RESTN___GREATER_IMPL =
 store_thm
  ("IMP_ON_PATH_RESTN___GREATER_IMPL",
   ``!v t a b. IMP_ON_PATH_RESTN t v a b = (!t'. t' >= t ==> IMP_ON_PATH_RESTN t' v a b)``,
   SIMP_TAC arith_ss [IMP_ON_PATH_RESTN_def] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      METIS_TAC[GREATER_EQ, LESS_EQ_TRANS],
      METIS_TAC[GREATER_EQ, LESS_EQ_REFL]
   ]);


val EQUIV_ON_PATH_RESTN___IMP_ON_PATH_RESTN =
 store_thm
  ("EQUIV_ON_PATH_RESTN___IMP_ON_PATH_RESTN",
   ``!t v a1 a2. (EQUIV_ON_PATH_RESTN t v a1 a2) =
      (IMP_ON_PATH_RESTN t v a1 a2 /\ IMP_ON_PATH_RESTN t v a2 a1)``,

   REWRITE_TAC[IMP_ON_PATH_RESTN_def, EQUIV_ON_PATH_RESTN_def] THEN
   METIS_TAC[]);


val EQUIV_ON_PATH_RESTN___GREATER_IMPL =
 store_thm
  ("EQUIV_ON_PATH_RESTN___GREATER_IMPL",
   ``!v t a b. EQUIV_ON_PATH_RESTN t v a b = (!t'. t' >= t ==> EQUIV_ON_PATH_RESTN t' v a b)``,
   METIS_TAC[IMP_ON_PATH_RESTN___GREATER_IMPL,EQUIV_ON_PATH_RESTN___IMP_ON_PATH_RESTN]);


val NAND_ON_PATH_RESTN___GREATER_IMPL =
 store_thm
  ("NAND_ON_PATH_RESTN___GREATER_IMPL",
   ``!v t a b. NAND_ON_PATH_RESTN t v a b = (!t'. t' >= t ==> NAND_ON_PATH_RESTN t' v a b)``,
   SIMP_TAC arith_ss [NAND_ON_PATH_RESTN_def] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      METIS_TAC[GREATER_EQ, LESS_EQ_TRANS],
      METIS_TAC[GREATER_EQ, LESS_EQ_REFL]
   ]);


val NOT_ON_PATH_RESTN___GREATER_IMPL =
 store_thm
  ("NOT_ON_PATH_RESTN___GREATER_IMPL",
   ``!v t a. NOT_ON_PATH_RESTN t v a = (!t'. t' >= t ==> NOT_ON_PATH_RESTN t' v a)``,
   SIMP_TAC arith_ss [NOT_ON_PATH_RESTN_def] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      METIS_TAC[GREATER_EQ, LESS_EQ_TRANS],
      METIS_TAC[GREATER_EQ, LESS_EQ_REFL]
   ]);


val IS_ON_PATH_RESTN___GREATER_IMPL =
 store_thm
  ("IS_ON_PATH_RESTN___GREATER_IMPL",
   ``!v t a. IS_ON_PATH_RESTN t v a = (?t0. (t <= t0) /\ (P_SEM (v t0) a) /\ (!t'. (t <= t' /\ t' <= t0) ==> IS_ON_PATH_RESTN t' v a))``,

   SIMP_TAC arith_ss [IS_ON_PATH_RESTN_def, NOT_ON_PATH_RESTN_def] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      EXISTS_TAC ``t':num`` THEN
      METIS_TAC[],

      EXISTS_TAC ``t0:num`` THEN
      METIS_TAC[]
   ]);


val EQUIV_PATH_RESTN___GREATER_IMPL =
 store_thm
  ("EQUIV_PATH_RESTN___GREATER_IMPL",
   ``!t v1 v2. EQUIV_PATH_RESTN t v1 v2 = (!t'. t' >= t ==> EQUIV_PATH_RESTN t' v1 v2)``,
   SIMP_TAC arith_ss [EQUIV_PATH_RESTN_def] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      METIS_TAC[GREATER_EQ, LESS_EQ_TRANS],
      METIS_TAC[GREATER_EQ, LESS_EQ_REFL]
   ]);


val EQUIV_PATH_RESTN___PATH_RESTN =
 store_thm
  ("EQUIV_PATH_RESTN___PATH_RESTN",
   ``!t v1 v2. (EQUIV_PATH_RESTN t v1 v2) = (PATH_RESTN v1 t = PATH_RESTN v2 t)``,
   SIMP_TAC arith_ss [EQUIV_PATH_RESTN_def, PATH_RESTN_def, EXTENSION] THEN
   ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
   SIMP_TAC std_ss [EXTENSION] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      `t <= t+x` by DECIDE_TAC THEN
      METIS_TAC[],

      `?x. t + x = l` by METIS_TAC[LESS_EQ_EXISTS] THEN
      METIS_TAC[]
   ]);


val EQUIV_PATH_RESTN_SYM =
 store_thm
  ("EQUIV_PATH_RESTN_SYM",
   ``!v1 v2 t. EQUIV_PATH_RESTN t v1 v2 = EQUIV_PATH_RESTN t v2 v1``,
   EVAL_TAC THEN PROVE_TAC[]);


val BEFORE_ON_PATH_STRONG___BEFORE_ON_PATH =
 store_thm
  ("BEFORE_ON_PATH_STRONG___BEFORE_ON_PATH",
   ``!v t a b. BEFORE_ON_PATH_RESTN_STRONG t v a b ==> BEFORE_ON_PATH_RESTN t v a b``,
   REWRITE_TAC [BEFORE_ON_PATH_RESTN_STRONG_def, BEFORE_ON_PATH_RESTN_def] THEN
   REPEAT STRIP_TAC THEN
   `?u. t <= u /\ u < t' /\ P_SEM (v u) a` by PROVE_TAC[] THEN
   EXISTS_TAC ``u:num`` THEN
   FULL_SIMP_TAC arith_ss []);

val NOT_ON_PATH___IMP_ON_PATH =
 store_thm
  ("NOT_ON_PATH___IMP_ON_PATH",
   ``!v t a1 a2. NOT_ON_PATH_RESTN t v a1 ==> IMP_ON_PATH_RESTN t v a1 a2``,

   METIS_TAC[NOT_ON_PATH_RESTN_def, IMP_ON_PATH_RESTN_def, GREATER_EQ]
);


val NOT_ON_PATH___BEFORE_ON_PATH_STRONG =
 store_thm
  ("NOT_ON_PATH___BEFORE_ON_PATH_STRONG",
   ``!v t a1 a2. NOT_ON_PATH_RESTN t v a2 ==> BEFORE_ON_PATH_RESTN_STRONG t v a1 a2``,

   PROVE_TAC[NOT_ON_PATH_RESTN_def, BEFORE_ON_PATH_RESTN_STRONG_def]
);


val BEFORE_ON_PATH_STRONG___LESS_IMPL =
 store_thm
  ("BEFORE_ON_PATH_STRONG___LESS_IMPL",
   ``!v t t2 a1 a2.
      (t <= t2 /\ (!j. (t <= j /\  j < t2) ==> ~(P_SEM (v j) a2)) /\
      BEFORE_ON_PATH_RESTN_STRONG t2 v a1 a2) ==> (BEFORE_ON_PATH_RESTN_STRONG t v a1 a2)``,

   REWRITE_TAC[BEFORE_ON_PATH_RESTN_STRONG_def] THEN
   REPEAT STRIP_TAC THEN
   `~(t' < t2)` by METIS_TAC[] THEN
   `t2 <= t'` by DECIDE_TAC THEN
   `?u. t2 <= u /\ u < t' /\ P_SEM (v u) a1` by METIS_TAC[] THEN
   EXISTS_TAC ``u:num`` THEN
   ASM_REWRITE_TAC[] THEN
   DECIDE_TAC);


val BEFORE_ON_PATH___LESS_IMPL =
 store_thm
  ("BEFORE_ON_PATH___LESS_IMPL",
   ``!v t t2 a1 a2.
      (t <= t2 /\ (!j. (t <= j /\  j < t2) ==> ~(P_SEM (v j) a2)) /\
      BEFORE_ON_PATH_RESTN t2 v a1 a2) ==> (BEFORE_ON_PATH_RESTN t v a1 a2)``,

   REWRITE_TAC[BEFORE_ON_PATH_RESTN_def] THEN
   REPEAT STRIP_TAC THEN
   `~(t' < t2)` by METIS_TAC[] THEN
   `t2 <= t'` by DECIDE_TAC THEN
   `?u. t2 <= u /\ u <= t' /\ P_SEM (v u) a1` by METIS_TAC[] THEN
   EXISTS_TAC ``u:num`` THEN
   ASM_REWRITE_TAC[] THEN
   DECIDE_TAC);


val BEFORE_ON_PATH_STRONG___GREATER_IMPL =
 store_thm
  ("BEFORE_ON_PATH_STRONG___GREATER_IMPL",
   ``!v t t2 a1 a2.
      (t <= t2 /\ (!j. (t <= j /\  j < t2) ==> ~(P_SEM (v j) a1)) /\
      BEFORE_ON_PATH_RESTN_STRONG t v a1 a2) ==> (BEFORE_ON_PATH_RESTN_STRONG t2 v a1 a2)``,

   REWRITE_TAC[BEFORE_ON_PATH_RESTN_STRONG_def] THEN
   REPEAT STRIP_TAC THEN
   `t <= t'` by DECIDE_TAC THEN
   `?u. t <= u /\ u < t' /\ P_SEM (v u) a1` by METIS_TAC[] THEN
   EXISTS_TAC ``u:num`` THEN
   ASM_REWRITE_TAC[] THEN
   `~(u < t2)` by METIS_TAC[] THEN
   DECIDE_TAC);


val BEFORE_ON_PATH___GREATER_IMPL =
 store_thm
  ("BEFORE_ON_PATH___GREATER_IMPL",
   ``!v t t2 a1 a2.
      (t <= t2 /\ (!j. (t <= j /\  j < t2) ==> ~(P_SEM (v j) a1)) /\
      BEFORE_ON_PATH_RESTN t v a1 a2) ==> (BEFORE_ON_PATH_RESTN t2 v a1 a2)``,

   REWRITE_TAC[BEFORE_ON_PATH_RESTN_def] THEN
   REPEAT STRIP_TAC THEN
   `t <= t'` by DECIDE_TAC THEN
   `?u. t <= u /\ u <= t' /\ P_SEM (v u) a1` by METIS_TAC[] THEN
   EXISTS_TAC ``u:num`` THEN
   ASM_REWRITE_TAC[] THEN
   `~(u < t2)` by METIS_TAC[] THEN
   DECIDE_TAC);


val BEFORE_ON_PATH___IMPL_START =
 store_thm
  ("BEFORE_ON_PATH___IMPL_START",
   ``!v t a1 a2. (BEFORE_ON_PATH_RESTN t v a1 a2 /\ P_SEM (v t) a2) ==> P_SEM (v t) a1``,

   REWRITE_TAC[BEFORE_ON_PATH_RESTN_def] THEN
   METIS_TAC[LESS_EQ_REFL, EQ_LESS_EQ]);


val BEFORE_ON_PATH___IMPL_START2 =
 store_thm
  ("BEFORE_ON_PATH___IMPL_START2",
   ``!v t a1 a2. P_SEM (v t) a1 ==> BEFORE_ON_PATH_RESTN t v a1 a2``,

   REWRITE_TAC[BEFORE_ON_PATH_RESTN_def] THEN
   METIS_TAC[LESS_EQ_REFL]);


val BEFORE_ON_PATH_STRONG___IMPL_START =
 store_thm
  ("BEFORE_ON_PATH_STRONG___IMPL_START",
   ``!v t a1 a2. (BEFORE_ON_PATH_RESTN_STRONG t v a1 a2) ==> ~P_SEM (v t) a2``,

   REWRITE_TAC[BEFORE_ON_PATH_RESTN_STRONG_def] THEN
   METIS_TAC[NOT_LESS, LESS_EQ_REFL]);


val BEFORE_ON_PATH_STRONG___IMPL_START2 =
 store_thm
  ("BEFORE_ON_PATH_STRONG___IMPL_START2",
   ``!v t a1 a2. P_SEM (v t) a1 /\  ~P_SEM (v t) a2 ==> BEFORE_ON_PATH_RESTN_STRONG t v a1 a2``,
   REWRITE_TAC[BEFORE_ON_PATH_RESTN_STRONG_def] THEN
   REPEAT STRIP_TAC THEN
   `~(t = t')` by PROVE_TAC[] THEN
   `t < t'` by DECIDE_TAC THEN
   EXISTS_TAC ``t:num`` THEN
   PROVE_TAC[LESS_EQ_REFL]);


val BEFORE_ON_PATH_CASES =
 store_thm
  ("BEFORE_ON_PATH_CASES",
   ``!v t a1 a2. BEFORE_ON_PATH_RESTN t v a1 a2 \/ BEFORE_ON_PATH_RESTN t v a2 a1``,

   REPEAT STRIP_TAC THEN
   Cases_on `BEFORE_ON_PATH_RESTN t v a1 a2` THENL [
      ASM_REWRITE_TAC[],

      ASM_REWRITE_TAC [] THEN
      FULL_SIMP_TAC arith_ss [BEFORE_ON_PATH_RESTN_def] THEN
      REPEAT STRIP_TAC THEN
      `~(t'' <= t')` by PROVE_TAC[] THEN
      `t' <= t''` by DECIDE_TAC THEN
      EXISTS_TAC ``t':num`` THEN
      PROVE_TAC[]
   ]);


val BEFORE_ON_PATH___SUC =
 store_thm
  ("BEFORE_ON_PATH___SUC",
   ``!v t a1 a2. BEFORE_ON_PATH_RESTN t v a1 a2  ==> (P_SEM (v t) a1 \/ BEFORE_ON_PATH_RESTN (SUC t) v a1 a2)``,

   REPEAT STRIP_TAC THENL [
      Cases_on `P_SEM (v t) a1` THENL [
         ASM_REWRITE_TAC[],

         FULL_SIMP_TAC arith_ss [BEFORE_ON_PATH_RESTN_def] THEN
         REPEAT STRIP_TAC THEN
         `t <= t'` by DECIDE_TAC THEN
         `?u. t <= u /\ u <= t' /\ P_SEM (v u) a1` by METIS_TAC[] THEN
         `~(u = t)` by METIS_TAC[] THEN
         `SUC t <= u` by DECIDE_TAC THEN
         METIS_TAC[]
      ]
   ]);


val BEFORE_ON_PATH_STRONG___SUC =
 store_thm
  ("BEFORE_ON_PATH_STRONG___SUC",
   ``!v t a1 a2. BEFORE_ON_PATH_RESTN_STRONG t v a1 a2  ==> (P_SEM (v t) a1 \/ BEFORE_ON_PATH_RESTN_STRONG (SUC t) v a1 a2)``,

   REPEAT STRIP_TAC THENL [
      Cases_on `P_SEM (v t) a1` THENL [
         ASM_REWRITE_TAC[],

         FULL_SIMP_TAC arith_ss [BEFORE_ON_PATH_RESTN_STRONG_def] THEN
         REPEAT STRIP_TAC THEN
         `t <= t'` by DECIDE_TAC THEN
         `?u. t <= u /\ u < t' /\ P_SEM (v u) a1` by METIS_TAC[] THEN
         `~(u = t)` by METIS_TAC[] THEN
         `SUC t <= u` by DECIDE_TAC THEN
         METIS_TAC[]
      ]
   ]);


val BEFORE_ON_PATH_RESTN___NEGATION_IMPL =
 store_thm
  ("BEFORE_ON_PATH_RESTN___NEGATION_IMPL",
   ``!t v a b. ~(BEFORE_ON_PATH_RESTN t v a b) ==> BEFORE_ON_PATH_RESTN_STRONG t v b a``,

   SIMP_TAC arith_ss [BEFORE_ON_PATH_RESTN_def, BEFORE_ON_PATH_RESTN_STRONG_def] THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC ``t':num`` THEN
   ASM_REWRITE_TAC[] THEN
   CCONTR_TAC THEN
   `t'' <= t'` by DECIDE_TAC THEN
   METIS_TAC[]);


val ELEMENTS_OF_PATH_NOT_EMPTY =
 store_thm
  ("ELEMENTS_OF_PATH_NOT_EMPTY",
    ``!w. ~(ELEMENTS_OF_PATH w = EMPTY)``,

    SIMP_TAC std_ss [ELEMENTS_OF_PATH_def, EXTENSION, GSPECIFICATION, NOT_IN_EMPTY]);


val INF_ELEMENTS_OF_PATH_NOT_EMPTY =
 store_thm
  ("INF_ELEMENTS_OF_PATH_NOT_EMPTY",
    ``!S. FINITE S ==> (!w. ((!n. w n IN S) ==> ~(INF_ELEMENTS_OF_PATH w = EMPTY)))``,

    PSet_ind.SET_INDUCT_TAC FINITE_INDUCT THEN1 REWRITE_TAC[NOT_IN_EMPTY] THEN

    REPEAT STRIP_TAC THEN
    Cases_on `e IN INF_ELEMENTS_OF_PATH w` THEN1 (
        METIS_TAC[NOT_IN_EMPTY]
    ) THEN
    SUBGOAL_THEN ``~(s:'a set = EMPTY)`` ASSUME_TAC THEN1 (
        CCONTR_TAC THEN
        FULL_SIMP_TAC arith_ss [INF_ELEMENTS_OF_PATH_def, EXTENSION, GSPECIFICATION,
            NOT_IN_EMPTY, IN_SING, IN_INSERT] THEN
        `SUC n > n` by DECIDE_TAC THEN
        PROVE_TAC[]
    ) THEN
    `?x. x IN s` by PROVE_TAC [MEMBER_NOT_EMPTY] THEN

    `?w'. w' = \n. if (w n = e) then x else w n` by METIS_TAC[] THEN
    SUBGOAL_THEN ``!n:num. w' n IN (s:'a set)`` ASSUME_TAC THEN1 (
        ASM_SIMP_TAC std_ss [] THEN
        REPEAT STRIP_TAC THEN
        Cases_on `w n = e` THEN ASM_REWRITE_TAC[] THEN
        PROVE_TAC[IN_INSERT]
    ) THEN

    SUBGOAL_THEN ``?n. !m. m > n ==> (w m = w' m)`` STRIP_ASSUME_TAC  THEN1 (
        FULL_SIMP_TAC std_ss [INF_ELEMENTS_OF_PATH_def, GSPECIFICATION] THEN
        PROVE_TAC[]
    ) THEN

    SUBGOAL_THEN ``INF_ELEMENTS_OF_PATH w = INF_ELEMENTS_OF_PATH w'`` ASSUME_TAC THEN1 (
        SIMP_TAC std_ss [INF_ELEMENTS_OF_PATH_def, EXTENSION, GSPECIFICATION] THEN
        REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
            `?n''. n'' > n /\ n'' > n'` by (EXISTS_TAC ``SUC(n + n')`` THEN DECIDE_TAC) THEN
            `?m. m > n'' /\ (w m = x') /\ (w' m = x')` by METIS_TAC[] THEN
            METIS_TAC[],

            `?n''. n'' > n /\ n'' > n'` by (EXISTS_TAC ``SUC(n + n')`` THEN DECIDE_TAC) THEN
            `?m. m > n'' /\ (w' m = x')` by METIS_TAC[] THEN
            `m > n /\ m > n'` by DECIDE_TAC THEN
            `w m = x'` by PROVE_TAC[] THEN
            METIS_TAC[]
        ]
    ) THEN

    PROVE_TAC[]);




val PATH_EXTENSION_EQUIV_THM =
 store_thm
  ("PATH_EXTENSION_EQUIV_THM",
   ``!w q P S. (PATH_SUBSET w S /\ ~(q IN S)) ==> (

      !w'. (w' = (PATH_EXTENSION w q P)) =
         ((PATH_SUBSET w' (q INSERT S)) /\
         ((PATH_DIFF w' {q}) = w) /\
         ((PATH_RESTRICT w' S) = w) /\
         (!n. (q IN (w' n)) = (P n))))``,

   REPEAT STRIP_TAC THEN EQ_TAC  THENL [
      REPEAT DISCH_TAC THEN
      ASM_SIMP_TAC std_ss [] THEN
      `S SUBSET q INSERT S` by SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT] THEN
      ONCE_REWRITE_TAC[FUN_EQ_THM, PATH_SUBSET_def] THEN
      SIMP_TAC std_ss [GSYM FORALL_AND_THM, PATH_EXTENSION_def] THEN
      GEN_TAC THEN
      Cases_on `P n` THEN (
        FULL_SIMP_TAC std_ss [PATH_DIFF_def, SUBSET_DEF, IN_INSERT, DIFF_DEF, EXTENSION, GSPECIFICATION,
          NOT_IN_EMPTY, PATH_RESTRICT_def, PATH_MAP_def, IN_INTER, PATH_SUBSET_def] THEN
        METIS_TAC[]
      ),

      REWRITE_TAC[PATH_EXTENSION_def] THEN
      ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
      REPEAT STRIP_TAC THEN
      Cases_on `P x` THEN (
        FULL_SIMP_TAC std_ss [PATH_DIFF_def, SUBSET_DEF, IN_INSERT, DIFF_DEF, EXTENSION, GSPECIFICATION,
          NOT_IN_EMPTY, PATH_RESTRICT_def, PATH_MAP_def, IN_INTER, PATH_SUBSET_def] THEN
        METIS_TAC[]
      )
  ]);


val PATH_VAR_RENAMING___ORIG_PATH_EXISTS =
 store_thm
  ("PATH_VAR_RENAMING___ORIG_PATH_EXISTS",

   ``!w f S. (PATH_SUBSET w (IMAGE f S)) ==> (?w'. (PATH_SUBSET w' S) /\ (w = PATH_VAR_RENAMING f w'))``,

   SIMP_TAC std_ss [IMAGE_DEF, PATH_SUBSET_def, PATH_VAR_RENAMING_def, PATH_MAP_def, SUBSET_DEF, GSPECIFICATION] THEN
   REPEAT STRIP_TAC THEN
   SUBGOAL_TAC `?w'. !x n. x IN (w' n) = ((f x) IN w n /\ x IN S)` THEN1 (
     Q_TAC EXISTS_TAC `\n:num x. (f x) IN w n /\ x IN S` THEN
     SIMP_TAC std_ss [IN_DEF]
   ) THEN
   Q_TAC EXISTS_TAC `w'` THEN
   REPEAT STRIP_TAC THENL [
      PROVE_TAC[],

      ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
      PROVE_TAC[]
   ]);


val IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE_def =
 Define
  `IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE p n0 n =
     !m. (m >= n0) ==> ((p m) = (p (m+n)))`;


val IS_ULTIMATIVELY_PERIODIC_PATH_def =
 Define
  `IS_ULTIMATIVELY_PERIODIC_PATH p  =
     ?n0 n. 0 < n /\ IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE p n0 n`;


val IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE___ALTERNATIVE_DEF =
 store_thm ("IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE___ALTERNATIVE_DEF",
  ``!p n0 n. 0 < n ==>
      (IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE p n0 n =
     (!m. p (n0 + m) = p (n0 + m MOD n)))``,

    SIMP_TAC std_ss [IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE_def] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Induct_on `m DIV n` THENL [
        REPEAT STRIP_TAC THEN
        `m = (m DIV n)*n + m MOD n` by PROVE_TAC[DIVISION] THEN
        UNDISCH_HD_TAC THEN
        GSYM_NO_TAC 2 THEN
        ASM_SIMP_TAC std_ss [],

        REPEAT STRIP_TAC THEN
        `m = (SUC v)*n + m MOD n` by PROVE_TAC[DIVISION] THEN
        SIMP_ALL_TAC std_ss [MULT] THEN
        `n <= m` by DECIDE_TAC THEN
        `n*1 = n` by DECIDE_TAC THEN
        `(m-n) DIV n = (SUC v) - 1` by METIS_TAC[DIV_SUB] THEN
        `(m-n) MOD n = m MOD n` by METIS_TAC[MOD_SUB] THEN
        `((SUC v) - 1) = v` by DECIDE_TAC THEN

        Q_SPECL_NO_ASSUM 9 [`m - n`, `n`] THEN
        UNDISCH_HD_TAC THEN
        ASM_SIMP_TAC std_ss [] THEN
        Q_SPEC_NO_ASSUM 6 `n0 + (m - n)` THEN
        FULL_SIMP_TAC arith_ss []
      ],

      `?m'. m' = m - n0` by METIS_TAC[] THEN
      `m = n0 + m'` by DECIDE_TAC THEN
      METIS_TAC[ADD_ASSOC, ADD_MODULUS]
    ]);


val CUT_PATH_PERIODICALLY_def =
 Define
  `CUT_PATH_PERIODICALLY p n0 n =
     \x. if (x < n0) then (p x) else (p (n0 + (x - n0) MOD n))`;


val CUT_PATH_PERIODICALLY___BEGINNING =
 store_thm ("CUT_PATH_PERIODICALLY___BEGINNING",
    ``!n0 n p t. (t < (n+n0)) ==> (((CUT_PATH_PERIODICALLY p n0 n) t) = (p t))``,

    SIMP_TAC std_ss [CUT_PATH_PERIODICALLY_def] THEN
    REPEAT STRIP_TAC THEN
    Cases_on `t < n0` THENL [
      ASM_REWRITE_TAC[],

      `t - n0 < n` by DECIDE_TAC THEN
      ASM_SIMP_TAC arith_ss [LESS_MOD]
    ]);


val CUT_PATH_PERIODICALLY_1 =
 store_thm ("CUT_PATH_PERIODICALLY_1",
    ``!n0 p t. (t >= n0) ==> (((CUT_PATH_PERIODICALLY p n0 1) t) = (p n0))``,

    ASM_SIMP_TAC arith_ss [CUT_PATH_PERIODICALLY_def]);



val CUT_PATH_PERIODICALLY___IS_ULTIMATIVELY_PERIODIC =
 store_thm ("CUT_PATH_PERIODICALLY___IS_ULTIMATIVELY_PERIODIC",
  ``!p n0 n. IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE (CUT_PATH_PERIODICALLY p n0 n) n0 n``,

    SIMP_TAC std_ss [IS_ULTIMATIVELY_PERIODIC_PATH___CONCRETE_def,
                    CUT_PATH_PERIODICALLY_def] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC arith_ss [] THEN
    Cases_on `n = 0` THENL [
      ASM_SIMP_TAC arith_ss [],

      `0 < n /\ ((m + n - n0) = (n + (m - n0)))` by DECIDE_TAC THEN
      ASM_SIMP_TAC std_ss [arithmeticTheory.ADD_MODULUS_RIGHT]
    ]);




val PATH_RESTRICT___CUT_PATH_PERIODICALLY =
  store_thm (
    "PATH_RESTRICT___CUT_PATH_PERIODICALLY",

    ``!p n0 n S.
    (PATH_RESTRICT (CUT_PATH_PERIODICALLY p n0 n) S) =
    (CUT_PATH_PERIODICALLY (PATH_RESTRICT p S) n0 n)``,

    ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
    REPEAT GEN_TAC THEN
    SIMP_TAC std_ss [CUT_PATH_PERIODICALLY_def, PATH_RESTRICT_def, PATH_MAP_def, COND_RAND]);


val PATH_SUBSET_RESTRICT = store_thm ("PATH_SUBSET_RESTRICT",
  ``!w S. PATH_SUBSET (PATH_RESTRICT w S) S``,
SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, INTER_SUBSET, PATH_SUBSET_def])


val _ = export_theory();
