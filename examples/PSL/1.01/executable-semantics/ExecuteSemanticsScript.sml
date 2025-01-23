(*****************************************************************************)
(* Create "ExecuteSemantics": a derived fixpoint-style executable semantics  *)
(*                                                                           *)
(* Created Wed Mar 19 19:01:20 GMT 2003                                      *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(******************************************************************************
* Load theories
* (commented out for compilation)
* Compile using "Holmake -I ../official-semantics -I ../regexp"
******************************************************************************)

(*
loadPath := "../official-semantics" :: "../regexp" :: !loadPath;
app load ["bossLib","metisLib","intLib","res_quanTools","pred_setLib",
          "rich_listTheory", "regexpLib", "PropertiesTheory"];
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib;

(******************************************************************************
* Open theories (comment out quietdec's for compilation)
******************************************************************************)

(*
quietdec := true;
*)

open bossLib metisLib listTheory rich_listTheory pred_setLib intLib
     arithmeticTheory whileTheory;
open regexpTheory matcherTheory;
open FinitePSLPathTheory PSLPathTheory SyntaxTheory SyntacticSugarTheory
     UnclockedSemanticsTheory ClockedSemanticsTheory PropertiesTheory;

(*
quietdec := false;
*)

(******************************************************************************
* Set default parsing to natural numbers rather than integers
******************************************************************************)
val _ = intLib.deprecate_int();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* A simpset fragment to rewrite away quantifiers restricted with :: (a to b)
******************************************************************************)
val resq_SS =
 simpLib.merge_ss
  [res_quanTools.resq_SS,
   rewrites [IN_DEF,num_to_def,xnum_to_def,LENGTH_def]];

val std_resq_ss   = simpLib.++ (std_ss,   resq_SS);
val arith_resq_ss = simpLib.++ (arith_ss, resq_SS);
val list_resq_ss  = simpLib.++ (list_ss,  resq_SS);

val arith_suc_ss = simpLib.++ (arith_ss, numSimps.SUC_FILTER_ss);

(*---------------------------------------------------------------------------*)
(* Symbolic tacticals.                                                       *)
(*---------------------------------------------------------------------------*)

infixr 0 || THENC ORELSEC ORELSER;

val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;

val pureDefine = with_flag (computeLib.auto_import_definitions, false) Define;

(******************************************************************************
* Start a new theory called "ExecuteSemantics"
******************************************************************************)
val _ = new_theory "ExecuteSemantics";
val _ = ParseExtras.temp_loose_equality()

(*
(******************************************************************************
* Boolean expression SEREs representing truth and falsity
******************************************************************************)
val S_TRUE_def  = Define `S_TRUE  = S_BOOL B_TRUE`;
val S_FALSE_def = Define `S_FALSE = S_BOOL B_FALSE`;
*)

(******************************************************************************
* Executable semantics of [f1 U f2]
*   w |= [f1 U f2]
*   <==>
*   |w| > 0 And (w |= f2  Or  (w |= f1  And  w^1 |= [f1 U f2]))
******************************************************************************)
val UF_SEM_F_UNTIL_REC =
 store_thm
  ("UF_SEM_F_UNTIL_REC",
   ``UF_SEM w (F_UNTIL(f1,f2)) =
      LENGTH w > 0
      /\
      (UF_SEM w f2
       \/
       (UF_SEM w f1 /\ UF_SEM (RESTN w 1) (F_UNTIL(f1,f2))))``,
   RW_TAC arith_resq_ss [UF_SEM_def]
    THEN Cases_on `w`
    THEN ONCE_REWRITE_TAC[arithmeticTheory.ONE]
    THEN RW_TAC arith_resq_ss
         [num_to_def,xnum_to_def,RESTN_def,REST_def,LENGTH_def]
    THEN EQ_TAC
    THEN RW_TAC arith_ss [GT]
    THENL
     [DECIDE_TAC,
      Cases_on `UF_SEM (FINITE l) f2`
       THEN RW_TAC std_ss []
       THEN Cases_on `k=0`
       THEN RW_TAC arith_ss []
       THEN FULL_SIMP_TAC std_ss [RESTN_def]
       THEN `0 < k` by DECIDE_TAC
       THEN RES_TAC
       THENL
        [PROVE_TAC[RESTN_def],
         `k - 1 < LENGTH l - 1` by DECIDE_TAC
          THEN Q.EXISTS_TAC `k-1`
          THEN RW_TAC arith_ss [LENGTH_TL]
          THENL
           [`k = SUC(k-1)` by DECIDE_TAC
             THEN ASSUM_LIST(fn thl => ASSUME_TAC(SUBS[el 1 thl] (el 8 thl)))
             THEN FULL_SIMP_TAC std_ss [RESTN_def,REST_def],
            `SUC j < k` by DECIDE_TAC
             THEN RES_TAC
             THEN FULL_SIMP_TAC std_ss [REST_def, RESTN_def]]],
      Q.EXISTS_TAC `0`
       THEN RW_TAC arith_ss [RESTN_def],
      `LENGTH (TL l) = LENGTH l - 1` by RW_TAC arith_ss [LENGTH_TL]
        THEN `SUC k < LENGTH l` by DECIDE_TAC
        THEN Q.EXISTS_TAC `SUC k`
        THEN RW_TAC std_ss [RESTN_def,REST_def]
        THEN Cases_on `j=0`
        THEN RW_TAC std_ss [RESTN_def]
        THEN `j - 1 < k` by DECIDE_TAC
        THEN RES_TAC
        THEN `j = SUC(j-1)` by DECIDE_TAC
        THEN POP_ASSUM(fn th => SUBST_TAC[th])
        THEN RW_TAC std_ss [RESTN_def,REST_def],
      Cases_on `UF_SEM (INFINITE f) f2`
       THEN RW_TAC std_ss []
       THEN Cases_on `k=0`
       THEN RW_TAC arith_ss []
       THEN FULL_SIMP_TAC std_ss [RESTN_def]
       THEN `0 < k` by DECIDE_TAC
       THEN RES_TAC
       THEN FULL_SIMP_TAC std_ss [RESTN_def,GSYM REST_def]
       THEN `k = SUC(k-1)` by DECIDE_TAC
       THEN ASSUM_LIST(fn thl => ASSUME_TAC(SUBS[el 1 thl] (el 7 thl)))
       THEN FULL_SIMP_TAC std_ss [RESTN_def]
       THEN Q.EXISTS_TAC `k-1`
       THEN RW_TAC std_ss []
       THEN `SUC j < k` by DECIDE_TAC
       THEN PROVE_TAC[RESTN_def],
      Q.EXISTS_TAC `0`
       THEN RW_TAC arith_ss [RESTN_def],
      Q.EXISTS_TAC `SUC k`
       THEN FULL_SIMP_TAC std_ss [GSYM REST_def]
       THEN RW_TAC std_ss [RESTN_def]
       THEN Cases_on `j=0`
       THEN RW_TAC std_ss [RESTN_def]
       THEN `j - 1 < k` by DECIDE_TAC
       THEN RES_TAC
       THEN `j = SUC(j-1)` by DECIDE_TAC
       THEN POP_ASSUM(fn th => SUBST_TAC[th])
       THEN RW_TAC std_ss [RESTN_def]]);

(******************************************************************************
* Executable semantics of {r}(f) on finite paths.
*
* First define w |=_n f
*
*   w |=_0 {r}(f)
*
*   w |=_{n+1} {r}(f)
*   <==>
*   w |=_n {r}(f)  And  (w^{0,n} |= r  Implies  w^n |= f)
*
* then
*
*   w |= {r}(f)  <==>  w |=_|w| {r}(f)
******************************************************************************)
val UF_SEM_F_SUFFIX_IMP_FINITE_REC_def =
 Define
  `(UF_SEM_F_SUFFIX_IMP_FINITE_REC w (r,f) 0 = T)
   /\
   (UF_SEM_F_SUFFIX_IMP_FINITE_REC w (r,f) (SUC n) =
     UF_SEM_F_SUFFIX_IMP_FINITE_REC w (r,f) n
     /\
     (US_SEM (SEL w (0, n)) r ==> UF_SEM (RESTN w n) f))`;

(******************************************************************************
* Form needed for computeLib.EVAL
******************************************************************************)
val UF_SEM_F_SUFFIX_IMP_FINITE_REC_AUX =
 store_thm
  ("UF_SEM_F_SUFFIX_IMP_FINITE_REC_AUX",
  ``UF_SEM_F_SUFFIX_IMP_FINITE_REC w (r,f) n =
     (n = 0) \/
     (UF_SEM_F_SUFFIX_IMP_FINITE_REC w (r,f) (n-1)
      /\
     (US_SEM (SEL w (0, (n-1))) r ==> UF_SEM (RESTN w (n-1)) f))``,
  Cases_on `n`
   THEN RW_TAC arith_ss [UF_SEM_F_SUFFIX_IMP_FINITE_REC_def]);

(******************************************************************************
* UF_SEM_F_SUFFIX_IMP_FINITE_REC_FORALL
*
*  (All j < n: w^{0,j} |= r Implies w^j |= f) = w |=_n {r}(f)
******************************************************************************)
local
val UF_SEM_F_SUFFIX_IMP_FINITE_REC_FORALL1 =
 prove
  (``(!j. j < n ==> US_SEM (SEL w (0,j)) r ==> UF_SEM (RESTN w j) f)
     ==>
     UF_SEM_F_SUFFIX_IMP_FINITE_REC w (r,f) n``,
   Induct_on `n`
    THEN RW_TAC arith_ss [UF_SEM_F_SUFFIX_IMP_FINITE_REC_def]);

val UF_SEM_F_SUFFIX_IMP_FINITE_REC_FORALL2 =
 prove
  (``UF_SEM_F_SUFFIX_IMP_FINITE_REC w (r,f) n
     ==>
     (!j. j < n ==> US_SEM (SEL w (0,j)) r ==> UF_SEM (RESTN w j) f)``,
   Induct_on `n`
    THEN RW_TAC arith_ss [UF_SEM_F_SUFFIX_IMP_FINITE_REC_def]
    THEN Cases_on `j=n`
    THEN RW_TAC std_ss []
    THEN `j < n` by DECIDE_TAC
    THEN PROVE_TAC[]);
in
val UF_SEM_F_SUFFIX_IMP_FINITE_REC_FORALL =
 store_thm
  ("UF_SEM_F_SUFFIX_IMP_FINITE_REC_FORALL",
   ``(!j. j < n ==> US_SEM (SEL w (0,j)) r ==> UF_SEM (RESTN w j) f)
     =
     UF_SEM_F_SUFFIX_IMP_FINITE_REC w (r,f) n``,
   PROVE_TAC[UF_SEM_F_SUFFIX_IMP_FINITE_REC_FORALL1,UF_SEM_F_SUFFIX_IMP_FINITE_REC_FORALL2]);
end;

(******************************************************************************
* w |= {r}(f)  <==>  w |=_|w| {r}(f)
******************************************************************************)
val UF_SEM_F_SUFFIX_IMP_FINITE_REC =
 store_thm
  ("UF_SEM_F_SUFFIX_IMP_FINITE_REC",
   ``UF_SEM (FINITE w) (F_SUFFIX_IMP(r,f)) =
      UF_SEM_F_SUFFIX_IMP_FINITE_REC (FINITE w) (r,f) (LENGTH w)``,
   RW_TAC list_resq_ss [UF_SEM_def]
    THEN PROVE_TAC[UF_SEM_F_SUFFIX_IMP_FINITE_REC_FORALL]);

(******************************************************************************
* Define w |=_x {r}(f) where x is an extended number (xnum)
******************************************************************************)
val UF_SEM_F_SUFFIX_IMP_REC_def =
 Define
  `(UF_SEM_F_SUFFIX_IMP_REC w (r,f) (XNUM n) =
     UF_SEM_F_SUFFIX_IMP_FINITE_REC w (r,f) n)
   /\
   (UF_SEM_F_SUFFIX_IMP_REC w (r,f) INFINITY =
     !n. US_SEM (SEL w (0,n)) r ==> UF_SEM (RESTN w n) f)`;

(******************************************************************************
* w |= {r}(f)  <==>  w |=_|w| {r}(f)  (for finite and infinite paths w)
******************************************************************************)
val UF_SEM_F_SUFFIX_IMP_REC =
 store_thm
  ("UF_SEM_F_SUFFIX_IMP_REC",
   ``UF_SEM w (F_SUFFIX_IMP(r,f)) =
      UF_SEM_F_SUFFIX_IMP_REC w (r,f) (LENGTH w)``,
   Cases_on `w`
    THEN RW_TAC list_resq_ss
          [UF_SEM_def,UF_SEM_F_SUFFIX_IMP_FINITE_REC,
           UF_SEM_F_SUFFIX_IMP_REC_def]);

(*---------------------------------------------------------------------------*)
(* Converting regexps from SyntaxTheory to regexpTheory.                     *)
(*---------------------------------------------------------------------------*)

val CONCAT_is_CONCAT = prove
  (``FinitePSLPath$CONCAT = regexp$CONCAT``,
   RW_TAC std_ss [FUN_EQ_THM]
   >> Induct_on `x`
   >> RW_TAC std_ss [FinitePSLPathTheory.CONCAT_def, regexpTheory.CONCAT_def]);

val RESTN_is_BUTFIRSTN = prove
  (``!n l. n <= LENGTH l ==> (RESTN l n = BUTFIRSTN n l)``,
   Induct_on `l`
   >- RW_TAC arith_ss [LENGTH, BUTFIRSTN, FinitePSLPathTheory.RESTN_def]
   >> GEN_TAC
   >> Cases >- RW_TAC arith_ss [LENGTH, BUTFIRSTN, FinitePSLPathTheory.RESTN_def]
   >> RW_TAC arith_ss
      [LENGTH, BUTFIRSTN, FinitePSLPathTheory.RESTN_def,
       FinitePSLPathTheory.REST_def, TL]);

val SEL_FINITE_is_BUTFIRSTN_FIRSTN = prove
  (``!j k l.
       j <= k /\ k < LENGTH l ==>
       (SEL (FINITE l) (j,k) = BUTFIRSTN j (FIRSTN (SUC k) l))``,
   SIMP_TAC std_ss [SEL_def]
   >> Induct_on `l` >- RW_TAC arith_ss [LENGTH, FIRSTN]
   >> GEN_TAC
   >> GEN_TAC
   >> Cases
   >- (ONCE_REWRITE_TAC [SEL_REC_AUX]
       >> RW_TAC arith_ss [LENGTH, FIRSTN, HEAD_def, HD]
       >> ONCE_REWRITE_TAC [SEL_REC_AUX]
       >> RW_TAC arith_ss [BUTFIRSTN])
   >> FULL_SIMP_TAC arith_ss [LENGTH]
   >> ONCE_REWRITE_TAC [SEL_REC_AUX]
   >> RW_TAC arith_ss
      [LENGTH, FIRSTN, arithmeticTheory.ADD1, HEAD_def, HD, REST_def, TL,
       BUTFIRSTN]
   >| [Q.PAT_X_ASSUM `!j. P j` (MP_TAC o Q.SPECL [`0`, `n`])
       >> RW_TAC arith_ss [BUTFIRSTN, arithmeticTheory.ADD1],
       Q.PAT_X_ASSUM `!j. P j` (MP_TAC o Q.SPECL [`j - 1`, `n`])
       >> RW_TAC arith_ss [BUTFIRSTN, arithmeticTheory.ADD1]
       >> Cases_on `j`
       >> RW_TAC arith_ss [BUTFIRSTN]]);

val sere2regexp_def = Define
  `(sere2regexp (S_BOOL b) = Atom (\l. B_SEM l b)) /\
   (sere2regexp (S_CAT (r1, r2)) = Cat (sere2regexp r1) (sere2regexp r2)) /\
   (sere2regexp (S_FUSION (r1, r2)) = Fuse (sere2regexp r1) (sere2regexp r2)) /\
   (sere2regexp (S_OR (r1, r2)) = Or (sere2regexp r1) (sere2regexp r2)) /\
   (sere2regexp (S_AND (r1, r2)) = And (sere2regexp r1) (sere2regexp r2)) /\
   (sere2regexp (S_REPEAT r) = Repeat (sere2regexp r))`;

val sere2regexp = prove
  (``!r l. S_CLOCK_FREE r ==> (US_SEM l r = sem (sere2regexp r) l)``,
   INDUCT_THEN sere_induct ASSUME_TAC
   >> RW_TAC std_ss
      [US_SEM_def, sem_def, sere2regexp_def, ELEM_EL, EL, S_CLOCK_FREE_def]
   >> CONV_TAC (DEPTH_CONV ETA_CONV)
   >> RW_TAC std_ss [CONCAT_is_CONCAT]);

val EVAL_US_SEM = store_thm
  ("EVAL_US_SEM",
   ``!l r.
       US_SEM l r =
       if S_CLOCK_FREE r then amatch (sere2regexp r) l else US_SEM l r``,
   RW_TAC std_ss [GSYM sere2regexp, amatch]);

(******************************************************************************
* w |= {r1} |-> {r2}!  <==>  w |= {r1}(not({r2}(F)))
******************************************************************************)
val EVAL_UF_SEM_F_SUFFIX_IMP = store_thm
  ("EVAL_UF_SEM_F_SUFFIX_IMP",
   ``!w r f.
       UF_SEM (FINITE w) (F_SUFFIX_IMP (r,f)) =
       if S_CLOCK_FREE r then acheck (sere2regexp r) (\x. UF_SEM (FINITE x) f) w
       else UF_SEM (FINITE w) (F_SUFFIX_IMP (r,f))``,
   RW_TAC list_resq_ss [acheck, UF_SEM_def, sere2regexp, RESTN_FINITE]
   >> RW_TAC arith_ss
      [RESTN_is_BUTFIRSTN, SEL_FINITE_is_BUTFIRSTN_FIRSTN, BUTFIRSTN]
   >> METIS_TAC []);

val FINITE_UF_SEM_F_STRONG_IMP_F_SUFFIX_IMP = store_thm
  ("FINITE_UF_SEM_F_STRONG_IMP_F_SUFFIX_IMP",
   ``!w r1 r2.
       UF_SEM (FINITE w) (F_STRONG_IMP (r1,r2)) =
       UF_SEM (FINITE w)
       (F_SUFFIX_IMP (r1, F_NOT (F_SUFFIX_IMP (r2, F_BOOL B_FALSE))))``,
   RW_TAC list_resq_ss [UF_SEM_def, B_SEM, AND_IMP_INTRO]
   >> HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``(!j. P j ==> (Q j = R j)) ==> ((!j. P j ==> Q j) = !j. P j ==> R j)``)
   >> RW_TAC std_ss []
   >> HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!R. (!k. P k ==> (?k'. k = k' + j)) /\ (!k. P (k + j) = Q k) ==>
             ((?j. P j) = ?j. Q j)``)
   >> CONJ_TAC
   >- (RW_TAC std_ss []
       >> Q.EXISTS_TAC `k - j`
       >> RW_TAC arith_ss [])
   >> RW_TAC arith_ss []
   >> Know `(j,j+j') = (j+0,j+j')` >- RW_TAC arith_ss []
   >> DISCH_THEN (fn th => REWRITE_TAC [th, GSYM SEL_RESTN])
   >> MATCH_MP_TAC (PROVE [] ``(a ==> (b = c)) ==> (b /\ a = c /\ a)``)
   >> STRIP_TAC
   >> RW_TAC arith_ss [xnum_to_def, RESTN_FINITE, LENGTH_def]
   >> RW_TAC arith_ss [FinitePSLPathTheory.LENGTH_RESTN]);

val INFINITE_UF_SEM_F_STRONG_IMP_F_SUFFIX_IMP = store_thm
  ("INFINITE_UF_SEM_F_STRONG_IMP_F_SUFFIX_IMP",
   ``!p r1 r2.
       UF_SEM (INFINITE p) (F_STRONG_IMP (r1,r2)) =
       UF_SEM (INFINITE p)
       (F_SUFFIX_IMP (r1, F_NOT (F_SUFFIX_IMP (r2, F_BOOL B_FALSE))))``,
   RW_TAC list_resq_ss [UF_SEM_def, B_SEM, AND_IMP_INTRO]
    THEN HO_MATCH_MP_TAC (* MJCG tried using >>, >|, but it wouldn't parse *)
          (METIS_PROVE []
           ``(!j. P j ==> (Q j = R j)) ==> ((!j. P j ==> Q j) = !j. P j ==> R j)``)
    THEN RW_TAC arith_ss [LENGTH_RESTN_INFINITE,xnum_to_def,SEL_RESTN]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL[Q.EXISTS_TAC `k-j`, Q.EXISTS_TAC `j+j'`]
    THEN RW_TAC arith_ss []);

val UF_SEM_F_STRONG_IMP_F_SUFFIX_IMP = store_thm
  ("UF_SEM_F_STRONG_IMP_F_SUFFIX_IMP",
   ``!w r1 r2.
       UF_SEM w (F_STRONG_IMP (r1,r2)) =
       UF_SEM w
       (F_SUFFIX_IMP (r1, F_NOT (F_SUFFIX_IMP (r2, F_BOOL B_FALSE))))``,
   Cases_on `w`
    THEN PROVE_TAC
          [FINITE_UF_SEM_F_STRONG_IMP_F_SUFFIX_IMP,
           INFINITE_UF_SEM_F_STRONG_IMP_F_SUFFIX_IMP]);

(******************************************************************************
* Weak implication
******************************************************************************)
val BUTFIRSTN_FIRSTN = prove
  (``!n k l.
       k + n <= LENGTH l ==>
       (BUTFIRSTN n (FIRSTN (k + n) l) = FIRSTN k (BUTFIRSTN n l))``,
   Induct
   >> GEN_TAC
   >> Cases
   >> RW_TAC arith_ss [BUTFIRSTN, FIRSTN, HD, TL, LENGTH, arithmeticTheory.ADD]
   >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o GSYM o Q.SPECL [`k`, `t`])
   >> RW_TAC arith_ss []
   >> RW_TAC arith_ss [BUTFIRSTN, FIRSTN, arithmeticTheory.ADD_CLAUSES]);

val UF_SEM_F_WEAK_IMP_FINITE = prove
  (``!w r1 r2.
       UF_SEM (FINITE w) (F_WEAK_IMP (r1,r2)) =
       !j :: (0 to LENGTH w).
         US_SEM (SEL (FINITE w) (0,j)) r1
         ==>
         (?k :: (j to LENGTH w). US_SEM (SEL (FINITE w) (j,k)) r2)
         \/
         ?w'. US_SEM (SEL (FINITE w) (j, LENGTH w - 1) <> w') r2``,
   RW_TAC list_resq_ss [UF_SEM_def]
   >> ONCE_REWRITE_TAC [PROVE [] ``a \/ b = ~a ==> b``]
   >> REWRITE_TAC [AND_IMP_INTRO]
   >> HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``(!j. A j ==> (B j = C j)) ==> ((!j. A j ==> B j) = !j. A j ==> C j)``)
   >> RW_TAC std_ss []
   >> EQ_TAC
   >- (DISCH_THEN (MP_TAC o Q.SPEC `LENGTH (w : ('a -> bool) list) - 1`)
       >> RW_TAC arith_ss [])
   >> RW_TAC std_ss []
   >> Cases_on `k = LENGTH w - 1` >- METIS_TAC []
   >> Q.EXISTS_TAC `SEL (FINITE w) (k + 1, LENGTH w - 1) <> w'`
   >> RW_TAC arith_ss [APPEND_ASSOC, GSYM SEL_SPLIT]);

val EVAL_UF_SEM_F_WEAK_IMP = store_thm
  ("EVAL_UF_SEM_F_WEAK_IMP",
   ``!w r1 r2.
       UF_SEM (FINITE w) (F_WEAK_IMP (r1,r2)) =
       if S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2 then
         acheck (sere2regexp r1)
         (\x.
            UF_SEM (FINITE x) (F_NOT (F_SUFFIX_IMP (r2, F_BOOL B_FALSE))) \/
            amatch (Prefix (sere2regexp r2)) x) w
       else UF_SEM (FINITE w) (F_WEAK_IMP (r1,r2))``,
   RW_TAC list_resq_ss
     [UF_SEM_F_WEAK_IMP_FINITE, acheck, amatch, sere2regexp]
   >> ONCE_REWRITE_TAC [UF_SEM_def]
   >> ONCE_REWRITE_TAC [EVAL_UF_SEM_F_SUFFIX_IMP]
   >> RW_TAC arith_ss
        [acheck, RESTN_is_BUTFIRSTN, SEL_FINITE_is_BUTFIRSTN_FIRSTN, sem_def,
         BUTFIRSTN]
   >> RW_TAC std_ss [AND_IMP_INTRO]
   >> HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``(!j. A j ==> (B j = C j)) ==> ((!j. A j ==> B j) = !j. A j ==> C j)``)
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC (PROVE [] ``(a = b) /\ (c = d) ==> (a \/ c = b \/ d)``)
   >> REVERSE CONJ_TAC
   >- (Know `SUC (LENGTH w - 1) = LENGTH w` >- DECIDE_TAC
       >> RW_TAC std_ss [FIRSTN_LENGTH_ID])
   >> RW_TAC arith_ss [UF_SEM_def, B_SEM]
   >> HO_MATCH_MP_TAC
      (METIS_PROVE []
       ``!f.
           (!j. A j ==> ?x. f x = j) /\ (!j. A (f j) = B j) ==>
           ((?j. A j) = ?j. B j)``)
   >> Q.EXISTS_TAC `\k. k + n`
   >> RW_TAC arith_ss [] >- (Q.EXISTS_TAC `k - n` >> RW_TAC arith_ss [])
   >> RW_TAC arith_ss [LENGTH_BUTFIRSTN]
   >> Cases_on `n + n' < LENGTH w`
   >> RW_TAC arith_ss [SEL_FINITE_is_BUTFIRSTN_FIRSTN]
   >> AP_TERM_TAC
   >> Know `SUC (n + n') <= LENGTH w` >- DECIDE_TAC
   >> POP_ASSUM_LIST (K ALL_TAC)
   >> Know `SUC (n + n') = SUC n' + n` >- DECIDE_TAC
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   >> METIS_TAC [BUTFIRSTN_FIRSTN]);

(******************************************************************************
* always{r} = {T[*]} |-> {r}
******************************************************************************)
val F_SERE_ALWAYS_def = Define
  `F_SERE_ALWAYS r = F_WEAK_IMP(S_REPEAT S_TRUE, r)`;

(******************************************************************************
* never{r} = {T[*];r} |-> {F}
******************************************************************************)
val F_SERE_NEVER_def = Define
  `F_SERE_NEVER r = F_WEAK_IMP(S_CAT(S_REPEAT S_TRUE, r), S_FALSE)`;

val F_SERE_NEVER_amatch = store_thm
  ("F_SERE_NEVER_amatch",
   ``!r w.
       S_CLOCK_FREE r /\ IS_INFINITE w ==>
       (UF_SEM w (F_SERE_NEVER r) =
        !n. ~amatch (sere2regexp (S_CAT (S_REPEAT S_TRUE,r))) (SEL w (0,n)))``,
   RW_TAC std_ss [F_SERE_NEVER_def]
   >> Know `LENGTH w = INFINITY`
   >- PROVE_TAC [PSLPathTheory.IS_INFINITE_EXISTS, PSLPathTheory.LENGTH_def]
   >> RW_TAC list_resq_ss [UF_SEM_def, xnum_to_def]
   >> Know `!l. US_SEM l S_FALSE = F`
   >- RW_TAC std_ss [US_SEM_def, S_FALSE_def, B_SEM]
   >> DISCH_THEN (fn th => RW_TAC std_ss [th])
   >> ONCE_REWRITE_TAC [EVAL_US_SEM]
   >> RW_TAC std_ss [S_CLOCK_FREE_def, S_TRUE_def]
   >> Suff `!j : num. (!k : num. ~(j <= k)) = F`
   >- DISCH_THEN (fn th => REWRITE_TAC [th])
   >> RW_TAC std_ss []
   >> PROVE_TAC [arithmeticTheory.LESS_EQ_REFL]);

(******************************************************************************
* Generating FSA checkers for the simple subset of PSL.
******************************************************************************)

(* Lemmas *)

val ELEM_SEL = store_thm
  ("ELEM_SEL",
   ``!w i. ELEM (SEL w (0,i)) 0 = ELEM w 0``,
   Cases
   >> RW_TAC arith_ss
      [FinitePSLPathTheory.ELEM_def, FinitePSLPathTheory.RESTN_def,
       FinitePSLPathTheory.HEAD_def, ELEM_def, RESTN_def, SEL_def]
   >> REWRITE_TAC [GSYM arithmeticTheory.ADD1, SEL_REC_def, HEAD_def, HD]);

val US_SEM_REPEAT_TRUE = store_thm
  ("US_SEM_REPEAT_TRUE",
   ``!w. US_SEM w (S_REPEAT S_TRUE)``,
   RW_TAC std_ss [US_SEM_def, B_SEM, S_TRUE_def]
   >> Q.EXISTS_TAC `MAP (\x. [x]) w`
   >> (RW_TAC std_ss [listTheory.EVERY_MAP, listTheory.LENGTH]
       >> RW_TAC std_ss [listTheory.EVERY_MEM])
   >> Induct_on `w`
   >> RW_TAC std_ss [CONCAT_def, MAP, APPEND]
   >> PROVE_TAC []);

val US_SEM_APPEND = store_thm
  ("US_SEM_APPEND",
   ``!r r' w w'.
       US_SEM w r /\ US_SEM w' r' ==> US_SEM (APPEND w w') (S_CAT (r,r'))``,
   RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [US_SEM_def]
   >> Q.EXISTS_TAC `w`
   >> Q.EXISTS_TAC `w'`
   >> RW_TAC std_ss []);

val CONCAT_EMPTY = store_thm
  ("CONCAT_EMPTY",
   ``!l. (FinitePSLPath$CONCAT l = []) = EVERY (\x. x = []) l``,
   Induct
   >> RW_TAC std_ss [CONCAT_def, listTheory.EVERY_DEF,
                     listTheory.APPEND_eq_NIL]);

val EMPTY_CONCAT = store_thm
  ("EMPTY_CONCAT",
   ``!l. ([] = FinitePSLPath$CONCAT l) = EVERY (\x. x = []) l``,
   PROVE_TAC [CONCAT_EMPTY]);

val S_FLEX_AND_EMPTY = store_thm
  ("S_FLEX_AND_EMPTY",
   ``!f g. US_SEM [] (S_FLEX_AND (f,g)) = US_SEM [] f /\ US_SEM [] g``,
   RW_TAC std_ss [US_SEM_def, S_FLEX_AND_def, S_TRUE_def, B_SEM,
                  listTheory.APPEND_eq_NIL, EMPTY_CONCAT,
                  GSYM listTheory.EVERY_CONJ]
   >> RW_TAC (simpLib.++ (arith_ss, boolSimps.CONJ_ss)) [LENGTH]
   >> RW_TAC std_ss [ALL_EL_F]);

val SEL_NIL = store_thm
  ("SEL_NIL",
   ``!n p. ~(SEL p (0,n) = [])``,
   RW_TAC arith_suc_ss [SEL_def, SEL_REC_def]);

val SEL_INIT_APPEND = store_thm
  ("SEL_INIT_APPEND",
   ``!p w.
       (?l n. SEL p (0,n) = APPEND w l) ==>
       (w = []) \/ (SEL p (0, LENGTH w - 1) = w)``,
   Induct_on `w` >- RW_TAC std_ss []
   >> RW_TAC std_ss []
   >> POP_ASSUM MP_TAC
   >> Cases_on `n`
   >- RW_TAC arith_suc_ss [APPEND, LENGTH, arithmeticTheory.PRE_SUB1,
                           listTheory.APPEND_eq_NIL, SEL_def, SEL_REC_def]
   >> Know `!l. ~(l = []) ==> (l = HD l :: TL l)`
   >- (Cases >> RW_TAC std_ss [HD, TL])
   >> DISCH_THEN (MP_TAC o Q.SPEC `SEL p (0,SUC n')`)
   >> SIMP_TAC std_ss [SEL_NIL]
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   >> RW_TAC std_ss [TL_SEL0, HD_SEL0, APPEND]
   >> Know `!l. ~(l = []) ==> (l = HD l :: TL l)`
   >- (Cases >> RW_TAC std_ss [HD, TL])
   >> DISCH_THEN (MP_TAC o Q.SPEC `SEL p (0, LENGTH (HEAD p :: w) - 1)`)
   >> SIMP_TAC std_ss [SEL_NIL]
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   >> RW_TAC arith_ss [TL_SEL0, HD_SEL0, LENGTH]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> Cases_on `LENGTH w`
   >- (POP_ASSUM MP_TAC
       >> RW_TAC arith_suc_ss [LENGTH_NIL, SEL_def, SEL_REC_def, TL])
   >> RW_TAC arith_ss [TL_SEL0]
   >> Know `~(w = [])`
   >- (STRIP_TAC
       >> Q.PAT_X_ASSUM `LENGTH w = SUC n` MP_TAC
       >> RW_TAC std_ss [LENGTH])
   >> REWRITE_TAC [IMP_DISJ_THM]
   >> FIRST_ASSUM MATCH_MP_TAC
   >> PROVE_TAC []);

val CAT_APPEND = store_thm
  ("CAT_APPEND",
   ``!a b c. CAT (a, CAT (b,c)) = CAT (a <> b, c)``,
   Induct >> RW_TAC std_ss [APPEND, CAT_def]);

val REST_CAT = store_thm
  ("REST_CAT",
   ``!l p. ~(l = []) ==> (REST (CAT (l,p)) = CAT (TL l, p))``,
   Induct >- RW_TAC std_ss []
   >> RW_TAC std_ss [CAT_def, REST_CONS, TL]);

val S_EMPTY_def = Define `S_EMPTY = S_REPEAT S_FALSE`;

val S_EMPTY = store_thm
  ("S_EMPTY",
   ``!p. US_SEM p S_EMPTY = (p = [])``,
   RW_TAC std_ss
   [US_SEM_def, S_EMPTY_def, listTheory.EVERY_MEM, S_FALSE_def,
    B_SEM, NO_MEM, CONCAT_def]);

val S_EMPTY_CAT = store_thm
  ("S_EMPTY_CAT",
   ``!p a. US_SEM p (S_CAT (S_EMPTY, a)) = US_SEM p a``,
   RW_TAC std_ss [US_SEM_def, S_EMPTY, APPEND]);

val S_OR_CAT = store_thm
  ("S_OR_CAT",
   ``!p a b c.
       US_SEM p (S_CAT (S_OR (a,b), c)) =
       US_SEM p (S_OR (S_CAT (a,c), S_CAT (b,c)))``,
   RW_TAC std_ss [US_SEM_def]
   >> PROVE_TAC []);

val S_REPEAT_UNWIND = store_thm
  ("S_REPEAT_UNWIND",
   ``!a p.
       US_SEM p (S_OR (S_EMPTY, S_CAT (a, S_REPEAT a))) =
       US_SEM p (S_REPEAT a)``,
   RW_TAC std_ss [US_SEM_def, S_EMPTY]
   >> EQ_TAC
   >| [STRIP_TAC
       >- (Q.EXISTS_TAC `[]`
           >> RW_TAC std_ss [CONCAT_def, listTheory.EVERY_DEF])
       >> Q.EXISTS_TAC `w1 :: wlist`
       >> RW_TAC std_ss [CONCAT_def, listTheory.EVERY_DEF],
       RW_TAC std_ss []
       >> Cases_on `wlist` >- RW_TAC std_ss [CONCAT_def]
       >> DISJ2_TAC
       >> Q.EXISTS_TAC `h`
       >> Q.EXISTS_TAC `FinitePSLPath$CONCAT t`
       >> FULL_SIMP_TAC std_ss [CONCAT_def, listTheory.EVERY_DEF]
       >> PROVE_TAC []]);

val S_REPEAT_CAT_UNWIND = store_thm
  ("S_REPEAT_CAT_UNWIND",
   ``!a b p.
       US_SEM p (S_OR (b, S_CAT (a, S_CAT (S_REPEAT a, b)))) =
       US_SEM p (S_CAT (S_REPEAT a, b))``,
   RW_TAC std_ss []
   >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [US_SEM_def]))
   >> CONV_TAC (LAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [GSYM S_EMPTY_CAT])))
   >> RW_TAC std_ss [GSYM S_CAT_ASSOC]
   >> RW_TAC std_ss [GSYM US_SEM_def, GSYM S_OR_CAT]
   >> ONCE_REWRITE_TAC [US_SEM_def]
   >> RW_TAC std_ss [GSYM S_REPEAT_UNWIND]);

val SEL_REC0 = store_thm
  ("SEL_REC0",
   ``!n p. SEL_REC (n + 1) 0 p = SEL p (0,n)``,
   RW_TAC arith_ss [SEL_def]);

Theorem S_FLEX_AND_SEL_REC:
  !p f g.
    (?n. US_SEM (SEL_REC n 0 p) (S_FLEX_AND (f,g))) =
    ?n.
      US_SEM (SEL_REC n 0 p)
             (S_AND (S_CAT (f, S_REPEAT S_TRUE), S_CAT (g, S_REPEAT S_TRUE)))
Proof
   RW_TAC std_ss [S_FLEX_AND_def, GSYM S_TRUE_def]
   >> EQ_TAC
   >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [US_SEM_def]))
       >> RW_TAC std_ss []
       >| [Q.EXISTS_TAC `n`
           >> POP_ASSUM MP_TAC
           >> ONCE_REWRITE_TAC [US_SEM_def]
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [US_SEM_def]
           >> RW_TAC std_ss [US_SEM_REPEAT_TRUE]
           >> PROVE_TAC [APPEND_NIL],
           Q.EXISTS_TAC `n`
           >> POP_ASSUM MP_TAC
           >> ONCE_REWRITE_TAC [US_SEM_def]
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [US_SEM_def]
           >> RW_TAC std_ss [US_SEM_REPEAT_TRUE]
           >> PROVE_TAC [APPEND_NIL]])
    >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [US_SEM_def]))
    >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [US_SEM_def]))
    >> RW_TAC std_ss [US_SEM_REPEAT_TRUE]
    >> Know `LENGTH w1 <= LENGTH w1' \/ LENGTH w1' <= LENGTH w1`
    >- DECIDE_TAC
    >> REWRITE_TAC [LESS_EQ_EXISTS]
    >> DISCH_THEN (STRIP_ASSUME_TAC o GSYM)
    >| [Q.EXISTS_TAC `LENGTH w1'`
        >> ONCE_REWRITE_TAC [US_SEM_def]
        >> DISJ2_TAC
        >> Know `n = LENGTH w1' + LENGTH w2'`
        >- METIS_TAC [LENGTH_APPEND, LENGTH_SEL_REC]
        >> RW_TAC std_ss []
        >> ONCE_REWRITE_TAC [US_SEM_def]
        >> REVERSE CONJ_TAC
        >- (Q.PAT_X_ASSUM `SEL_REC A B C = w1' <> w2'` MP_TAC
            >> ONCE_REWRITE_TAC [ADD_COMM]
            >> ONCE_REWRITE_TAC [SEL_REC_SPLIT]
            >> RW_TAC arith_ss [APPEND_LENGTH_EQ, LENGTH_SEL_REC])
        >> Know `LENGTH w1' + LENGTH w2' = LENGTH w1 + LENGTH w2`
        >- METIS_TAC [listTheory.LENGTH_APPEND, LENGTH_SEL_REC]
        >> STRIP_TAC
        >> rename [‘LENGTH w1 + p' = LENGTH w1'’]
        >> Know `p' + LENGTH w2' = LENGTH w2`
        >- DECIDE_TAC
        >> POP_ASSUM (K ALL_TAC)
        >> STRIP_TAC
        >> Q.PAT_X_ASSUM `SEL_REC A B C = D` (K ALL_TAC)
        >> Q.PAT_X_ASSUM `SEL_REC A B C = D` MP_TAC
        >> Q.PAT_X_ASSUM `A = LENGTH w1'`(fn th => REWRITE_TAC [GSYM th])
        >> ASM_REWRITE_TAC [GSYM ADD_ASSOC]
        >> ONCE_REWRITE_TAC [ADD_COMM]
        >> ONCE_REWRITE_TAC [SEL_REC_SPLIT]
        >> ONCE_REWRITE_TAC [US_SEM_def]
        >> RW_TAC arith_ss
           [US_SEM_REPEAT_TRUE, APPEND_LENGTH_EQ, LENGTH_SEL_REC]
        >> PROVE_TAC [],
        Q.EXISTS_TAC `LENGTH w1`
        >> ONCE_REWRITE_TAC [US_SEM_def]
        >> DISJ1_TAC
        >> Know `n = LENGTH w1 + LENGTH w2`
        >- METIS_TAC [LENGTH_APPEND, LENGTH_SEL_REC]
        >> RW_TAC std_ss []
        >> ONCE_REWRITE_TAC [US_SEM_def]
        >> CONJ_TAC
        >- (Q.PAT_X_ASSUM `SEL_REC A B C = w1 <> w2` MP_TAC
            >> ONCE_REWRITE_TAC [ADD_COMM]
            >> ONCE_REWRITE_TAC [SEL_REC_SPLIT]
            >> RW_TAC arith_ss [APPEND_LENGTH_EQ, LENGTH_SEL_REC])
        >> Know `LENGTH w1' + LENGTH w2' = LENGTH w1 + LENGTH w2`
        >- METIS_TAC [listTheory.LENGTH_APPEND, LENGTH_SEL_REC]
        >> STRIP_TAC
        >> rename [‘LENGTH w1' + p' = LENGTH w1’]
        >> Know `p' + LENGTH w2 = LENGTH w2'`
        >- DECIDE_TAC
        >> POP_ASSUM (K ALL_TAC)
        >> STRIP_TAC
        >> Q.PAT_X_ASSUM `SEL_REC A B C = D` MP_TAC
        >> Q.PAT_X_ASSUM `SEL_REC A B C = D` (K ALL_TAC)
        >> Q.PAT_X_ASSUM `A = LENGTH w1`(fn th => REWRITE_TAC [GSYM th])
        >> ASM_REWRITE_TAC [GSYM ADD_ASSOC]
        >> ONCE_REWRITE_TAC [ADD_COMM]
        >> ONCE_REWRITE_TAC [SEL_REC_SPLIT]
        >> ONCE_REWRITE_TAC [US_SEM_def]
        >> RW_TAC arith_ss
           [US_SEM_REPEAT_TRUE, APPEND_LENGTH_EQ, LENGTH_SEL_REC]
        >> PROVE_TAC []]
QED

val S_FLEX_AND_SEL = store_thm
  ("S_FLEX_AND_SEL",
   ``!p f g.
       US_SEM [] (S_FLEX_AND (f,g)) \/
       (?n. US_SEM (SEL p (0,n)) (S_FLEX_AND (f,g))) =
       ?n.
         US_SEM (SEL p (0,n))
         (S_AND (S_CAT (f, S_REPEAT S_TRUE), S_CAT (g, S_REPEAT S_TRUE)))``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`p`, `f`, `g`] S_FLEX_AND_SEL_REC)
   >> Know `!P Q.
              ((?n. P n) = ?n. Q n) =
              (P 0 \/ (?n. P (SUC n)) = Q 0 \/ ?n. Q (SUC n))`
   >- METIS_TAC [num_CASES]
   >> DISCH_THEN (fn th => SIMP_TAC std_ss [th])
   >> MATCH_MP_TAC
      (PROVE []
       ``(A = B) /\ (C = D) /\ (E = G) ==> ((A \/ C = E) ==> (B \/ D = G))``)
   >> CONJ_TAC >- SIMP_TAC arith_ss [SEL_REC_def]
   >> CONJ_TAC >- RW_TAC arith_ss [SEL_def, ADD1]
   >> SIMP_TAC arith_ss [SEL_def, ADD1]
   >> MATCH_MP_TAC (PROVE [] ``(B ==> A) ==> (B \/ A = A)``)
   >> ONCE_REWRITE_TAC [US_SEM_def]
   >> ONCE_REWRITE_TAC [US_SEM_def]
   >> RW_TAC std_ss [SEL_REC_def, US_SEM_REPEAT_TRUE, APPEND_eq_NIL]
   >> Q.EXISTS_TAC `0`
   >> PROVE_TAC [APPEND]);

val S_FLEX_AND = store_thm
  ("S_FLEX_AND",
   ``!p f g.
       (?n. US_SEM (SEL_REC n 0 p) (S_FLEX_AND (f,g))) =
       (?n. US_SEM (SEL_REC n 0 p) f) /\ (?n. US_SEM (SEL_REC n 0 p) g)``,
   RW_TAC std_ss [S_FLEX_AND_SEL_REC]
   >> ONCE_REWRITE_TAC [US_SEM_def]
   >> ONCE_REWRITE_TAC [US_SEM_def]
   >> RW_TAC std_ss [US_SEM_REPEAT_TRUE]
   >> EQ_TAC
   >| [RW_TAC std_ss []
       >| [Know `n = LENGTH w2 + LENGTH w1`
           >- PROVE_TAC [LENGTH_APPEND, LENGTH_SEL_REC, ADD_COMM]
           >> RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `X = Y` (K ALL_TAC)
           >> Q.PAT_X_ASSUM `X = Y` MP_TAC
           >> RW_TAC arith_ss [SEL_REC_SPLIT, APPEND_LENGTH_EQ, LENGTH_SEL_REC]
           >> PROVE_TAC [],
           Know `n = LENGTH w2' + LENGTH w1'`
           >- PROVE_TAC [LENGTH_APPEND, LENGTH_SEL_REC, ADD_COMM]
           >> RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `X = Y` MP_TAC
           >> Q.PAT_X_ASSUM `X = Y` (K ALL_TAC)
           >> RW_TAC arith_ss [SEL_REC_SPLIT, APPEND_LENGTH_EQ, LENGTH_SEL_REC]
           >> PROVE_TAC []],
       RW_TAC std_ss []
       >> Know `n <= n' \/ n' <= n` >- DECIDE_TAC
       >> REWRITE_TAC [LESS_EQ_EXISTS]
       >> DISCH_THEN (STRIP_ASSUME_TAC o GSYM)
       >| [Q.EXISTS_TAC `n'`
           >> REVERSE CONJ_TAC >- PROVE_TAC [APPEND_NIL]
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC arith_ss [SEL_REC_SPLIT]
           >> PROVE_TAC [APPEND_LENGTH_EQ, LENGTH_SEL_REC],
           Q.EXISTS_TAC `n`
           >> CONJ_TAC >- PROVE_TAC [APPEND_NIL]
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC arith_ss [SEL_REC_SPLIT]
           >> PROVE_TAC [APPEND_LENGTH_EQ, LENGTH_SEL_REC]]]);

val S_CAT_SEL_REC = store_thm
  ("S_CAT_SEL_REC",
   ``!p s t.
       (?n. US_SEM (SEL_REC n 0 p) (S_CAT (s,t))) =
       (?m. US_SEM (SEL_REC m 0 p) s /\
            ?n. US_SEM (SEL_REC n 0 (RESTN p m)) t)``,
   RW_TAC std_ss [US_SEM_def]
   >> EQ_TAC
   >| [RW_TAC std_ss []
       >> Know `n = LENGTH w2 + LENGTH w1`
       >- PROVE_TAC [LENGTH_SEL_REC, LENGTH_APPEND, ADD_COMM]
       >> RW_TAC std_ss []
       >> FULL_SIMP_TAC arith_ss
          [SEL_REC_SPLIT, APPEND_LENGTH_EQ, LENGTH_SEL_REC]
       >> Q.EXISTS_TAC `LENGTH w1`
       >> RW_TAC std_ss []
       >> Q.EXISTS_TAC `LENGTH w2`
       >> RW_TAC arith_ss [SEL_REC_RESTN],
       RW_TAC std_ss []
       >> Q.EXISTS_TAC `n + m`
       >> Q.EXISTS_TAC `SEL_REC m 0 p`
       >> Q.EXISTS_TAC `SEL_REC n 0 (RESTN p m)`
       >> RW_TAC arith_ss [SEL_REC_SPLIT, SEL_REC_RESTN]]);

val S_FUSION_SEL_REC = store_thm
  ("S_FUSION_SEL_REC",
   ``!p s t.
       (?n. US_SEM (SEL_REC n 0 p) (S_FUSION (s,t))) =
       (?m. US_SEM (SEL_REC (m + 1) 0 p) s /\
            ?n. US_SEM (SEL_REC (n + 1) 0 (RESTN p m)) t)``,
   RW_TAC std_ss [US_SEM_def]
   >> EQ_TAC
   >| [RW_TAC std_ss []
       >> Know `n = LENGTH w2 + LENGTH [l] + LENGTH w1`
       >- METIS_TAC [LENGTH_SEL_REC, LENGTH_APPEND, ADD_COMM, ADD_ASSOC]
       >> RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `X = Y`
          (MP_TAC o SIMP_RULE arith_ss
           [SEL_REC_SPLIT, APPEND_LENGTH_EQ, LENGTH_SEL_REC, APPEND_ASSOC,
            LENGTH_APPEND])
       >> RW_TAC std_ss [LENGTH]
       >> Q.EXISTS_TAC `LENGTH w1`
       >> CONJ_TAC
       >- (ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC arith_ss [SEL_REC_SPLIT])
       >> Q.EXISTS_TAC `LENGTH w2`
       >> RW_TAC arith_ss [SEL_REC_RESTN]
       >> RW_TAC arith_ss [SEL_REC_SPLIT],
       RW_TAC std_ss []
       >> Q.EXISTS_TAC `n + 1 + m`
       >> Q.EXISTS_TAC `SEL_REC m 0 p`
       >> Q.EXISTS_TAC `SEL_REC n 0 (RESTN p (m + 1))`
       >> Q.EXISTS_TAC `ELEM p m`
       >> ASM_SIMP_TAC arith_ss [APPEND_11, SEL_REC_SPLIT, GSYM APPEND_ASSOC]
       >> Know `[ELEM p m] = SEL_REC 1 0 (RESTN p m)`
       >- RW_TAC bool_ss [ELEM_def, SEL_REC_def, ONE]
       >> DISCH_THEN (fn th => REWRITE_TAC [th])
       >> CONJ_TAC >- RW_TAC arith_ss [SEL_REC_RESTN]
       >> CONJ_TAC
       >- (Q.PAT_X_ASSUM `US_SEM X s` MP_TAC
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC arith_ss [SEL_REC_RESTN, SEL_REC_SPLIT])
       >> POP_ASSUM MP_TAC
       >> SIMP_TAC arith_ss [SEL_REC_SPLIT]
       >> RW_TAC arith_ss [SEL_REC_RESTN]]);

val S_CAT_SEL_REC0 = store_thm
  ("S_CAT_SEL_REC0",
   ``!p s t n.
       US_SEM (SEL_REC n 0 p) (S_CAT (s,t)) =
       (?m.
         m <= n /\
         US_SEM (SEL_REC m 0 p) s /\
         US_SEM (SEL_REC (n - m) 0 (RESTN p m)) t)``,
   RW_TAC std_ss [US_SEM_def]
   >> EQ_TAC
   >| [RW_TAC std_ss []
       >> Know `n = LENGTH w2 + LENGTH w1`
       >- PROVE_TAC [LENGTH_SEL_REC, LENGTH_APPEND, ADD_COMM]
       >> RW_TAC std_ss []
       >> FULL_SIMP_TAC arith_ss
            [SEL_REC_SPLIT, APPEND_LENGTH_EQ, LENGTH_SEL_REC]
       >> Q.EXISTS_TAC `LENGTH w1`
       >> RW_TAC arith_ss []
       >> RW_TAC arith_ss [SEL_REC_RESTN],
       RW_TAC std_ss []
       >> Q.EXISTS_TAC `SEL_REC m 0 p`
       >> Q.EXISTS_TAC `SEL_REC (n - m) 0 (RESTN p m)`
       >> RW_TAC arith_ss [SEL_REC_RESTN]
       >> MP_TAC (Q.SPECL [`p`, `n - m`, `m`, `0`]
                  (GEN_ALL (INST_TYPE [alpha |-> ``:'a -> bool``]
                            (GSYM SEL_REC_SPLIT))))
       >> RW_TAC arith_ss []]);

val RESTN_CAT = store_thm
  ("RESTN_CAT",
   ``!l p n. (LENGTH l = n) ==> (RESTN (CAT (l,p)) n = p)``,
   Induct
   >> RW_TAC std_ss [CAT_def, LENGTH]
   >> RW_TAC std_ss [RESTN_def, REST_CONS]);

val CONS_HEAD_REST = store_thm
  ("CONS_HEAD_REST",
   ``!p. LENGTH p > 0 ==> (CONS (HEAD p, REST p) = p)``,
   Cases
   >> RW_TAC arith_ss [LENGTH_def, GT, REST_def, CONS_def, HEAD_def, FUN_EQ_THM]
   >> PROVE_TAC [CONS, LENGTH_NOT_NULL, GREATER_DEF]);

val CAT_SEL_REC_RESTN = store_thm
  ("CAT_SEL_REC_RESTN",
   ``!n p. IS_INFINITE p ==> (CAT (SEL_REC n 0 p, RESTN p n) = p)``,
   Induct
   >> RW_TAC std_ss [CAT_def, SEL_REC_def, RESTN_def, IS_INFINITE_REST]
   >> PROVE_TAC [CONS_HEAD_REST, GT, LENGTH_def, IS_INFINITE_EXISTS]);

val SEL_REC_CAT_0 = store_thm
  ("SEL_REC_CAT_0",
   ``!n l p. (LENGTH l = n) ==> (SEL_REC n 0 (CAT (l,p)) = l)``,
   Induct_on `l`
   >> RW_TAC std_ss [LENGTH]
   >> RW_TAC std_ss [SEL_REC_def, CAT_def, HEAD_CONS, REST_CONS]);

val SEL_REC_CAT = store_thm
  ("SEL_REC_CAT",
   ``!n m l p. (LENGTH l = n) ==> (SEL_REC m n (CAT (l,p)) = SEL_REC m 0 p)``,
   Induct_on `l`
   >> RW_TAC std_ss [LENGTH]
   >> Cases_on `m`
   >> RW_TAC std_ss [SEL_REC_def, CAT_def, HEAD_CONS, REST_CONS]);

val UF_SEM_F_W_ALT = store_thm
  ("UF_SEM_F_W_ALT",
   ``!f g w.
       UF_SEM w (F_W (f,g)) =
       !j :: 0 to LENGTH w.
         ~UF_SEM (RESTN w j) f ==> ?k :: 0 to SUC j. UF_SEM (RESTN w k) g``,
   RW_TAC std_ss []
   >> (Cases_on `w` (* 2 subgoals *)
       >> RW_TAC arith_resq_ss
            [UF_SEM_F_W, UF_SEM_def, UF_SEM_F_G, xnum_to_def]
       >> `!m n. (m:num) < SUC n = m <= n` by DECIDE_TAC
       >> ASM_REWRITE_TAC [])
   >| [REVERSE EQ_TAC
       >- (RW_TAC std_ss []
           >> MATCH_MP_TAC (PROVE [] ``(~b ==> a) ==> a \/ b``)
           >> SIMP_TAC std_ss []
           >> DISCH_THEN (MP_TAC o HO_MATCH_MP LEAST_EXISTS_IMP)
           >> Q.SPEC_TAC
              (`LEAST i. i < LENGTH l /\ ~UF_SEM (RESTN (FINITE l) i) f`,`i`)
           >> RW_TAC arith_ss [GSYM AND_IMP_INTRO]
           >> Q.PAT_X_ASSUM `!j. P j ==> Q j ==> R j` (MP_TAC o Q.SPEC `i`)
           >> RW_TAC arith_ss []
           >> Q.EXISTS_TAC `k`
           >> RW_TAC arith_ss [])
       >> RW_TAC std_ss []
       >- (Q.EXISTS_TAC `k`
           >> RW_TAC arith_ss []
           >> Know `!m n. (m:num) <= (n:num) \/ n < m` >- DECIDE_TAC
           >> METIS_TAC [])
       >> METIS_TAC [],
       REVERSE EQ_TAC
       >- (RW_TAC std_ss []
           >> MATCH_MP_TAC (PROVE [] ``(~b ==> a) ==> a \/ b``)
           >> SIMP_TAC std_ss []
           >> DISCH_THEN (MP_TAC o HO_MATCH_MP LEAST_EXISTS_IMP)
           >> Q.SPEC_TAC (`LEAST i. ~UF_SEM (RESTN (INFINITE f') i) f`,`i`)
           >> RW_TAC arith_ss []
           >> Q.PAT_X_ASSUM `!j. P j ==> ?k. Q j k` (MP_TAC o Q.SPEC `i`)
           >> RW_TAC arith_ss []
           >> Q.EXISTS_TAC `k`
           >> RW_TAC arith_ss [])
       >> RW_TAC std_ss []
       >- (Q.EXISTS_TAC `k`
           >> RW_TAC arith_ss []
           >> Know `!m n. (m:num) <= (n:num) \/ n < m` >- DECIDE_TAC
           >> METIS_TAC [])
       >> METIS_TAC []]);

val UF_SEM_WEAK_UNTIL = store_thm
  ("UF_SEM_WEAK_UNTIL",
   ``!p f g.
       UF_SEM p
       (F_NOT (F_AND (F_NOT (F_UNTIL (f,g)),F_UNTIL (F_BOOL B_TRUE,F_NOT f)))) =
       UF_SEM p (F_W (f,g))``,
   RW_TAC std_ss [UF_SEM_def, F_W_def, F_OR_def, F_G_def, F_F_def]);

val LENGTH_IS_INFINITE = store_thm
  ("LENGTH_IS_INFINITE",
   ``!p. IS_INFINITE p ==> (LENGTH p = INFINITY)``,
   METIS_TAC [LENGTH_def, IS_INFINITE_EXISTS]);

(* Safety violations *)

val safety_violation_def = Define
  `safety_violation p (f : 'a fl) =
   ?n. !q. IS_INFINITE q ==> ~UF_SEM (CAT (SEL_REC n 0 p, q)) f`;

val safety_violation_alt = store_thm
  ("safety_violation_alt",
   ``!p f.
       safety_violation p f =
       ?n. !w. ~UF_SEM (CAT (SEL_REC n 0 p, INFINITE w)) f``,
   REPEAT STRIP_TAC
   >> REWRITE_TAC [safety_violation_def]
   >> PROVE_TAC [IS_INFINITE_EXISTS, path_nchotomy, IS_INFINITE_def]);

val safety_violation = store_thm
  ("safety_violation",
   ``!p f.
       safety_violation p f =
       ?n. !q. IS_INFINITE q ==> ~UF_SEM (CAT (SEL p (0,n), q)) f``,
   REPEAT STRIP_TAC
   >> SIMP_TAC arith_ss [safety_violation_def, SEL_def]
   >> REVERSE EQ_TAC >- PROVE_TAC []
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> REVERSE (Cases_on `n`) >- PROVE_TAC [ADD1]
   >> SIMP_TAC std_ss [SEL_REC_def, CAT_def]
   >> PROVE_TAC [IS_INFINITE_CAT]);

val safety_violation_aux = store_thm
  ("safety_violation_aux",
   ``!p f.
       safety_violation p f =
       ?n. !w. ~UF_SEM (CAT (SEL p (0,n), INFINITE w)) f``,
   REPEAT STRIP_TAC
   >> REWRITE_TAC [safety_violation]
   >> PROVE_TAC [IS_INFINITE_EXISTS, path_nchotomy, IS_INFINITE_def]);

val safety_violation_refl = store_thm
  ("safety_violation_refl",
   ``!p f. IS_INFINITE p /\ safety_violation p f ==> ~UF_SEM p f``,
   RW_TAC std_ss [safety_violation_alt]
   >> MP_TAC (Q.SPECL [`n`, `p`]
              (INST_TYPE [alpha |-> ``:'a->bool``] CAT_SEL_REC_RESTN))
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   >> PROVE_TAC [IS_INFINITE_EXISTS, IS_INFINITE_RESTN]);

val safety_violation_NOT_NOT = store_thm
  ("safety_violation_NOT_NOT",
   ``!f p. safety_violation p (F_NOT (F_NOT f)) = safety_violation p f``,
   RW_TAC std_ss [safety_violation_def, UF_SEM_def]);

val safety_violation_WEAK_UNTIL = store_thm
  ("safety_violation_WEAK_UNTIL",
   ``!p f g.
       safety_violation p
       (F_NOT (F_AND (F_NOT (F_UNTIL (f,g)),F_UNTIL (F_BOOL B_TRUE,F_NOT f)))) =
       safety_violation p (F_W (f,g))``,
   RW_TAC std_ss [safety_violation_def, UF_SEM_WEAK_UNTIL]);

(* The simple subset *)

val boolean_def = Define
  `(boolean (F_BOOL _) = T) /\
   (boolean (F_NOT f) = boolean f) /\
   (boolean (F_AND (f,g)) = boolean f /\ boolean g) /\
   (boolean _ = F)`;

(*
  Cannot allow F_STRONG_IMP as simple formulas, because

    F_STRONG_IMP (S_TRUE, S_CAT (S_REPEAT (S_BOOL P), S_FALSE))

  doesn't have a finite bad prefix on P P P P P P P ..., and also

    F_AND (F_STRONG_IMP (S_TRUE, S_CAT (S_REPEAT (S_BOOL P), S_BOOL Q)),
           F_STRONG_IMP (S_TRUE, S_CAT (S_REPEAT (S_BOOL P), S_BOOL (B_NOT Q))))

  is "pathologically safe" [Kuperferman & Vardi 1999], meaning that the path

    P P P P P P P P ...

  has a bad prefix [] for the property, but there are no bad prefixes for
  either of the conjuncts.
*)

val simple_def = Define
  `(simple (F_BOOL b) = boolean (F_BOOL b)) /\
   (simple (F_NOT (F_NOT f)) = simple f) /\
   (simple (F_NOT (F_AND (F_NOT (F_UNTIL (f,g)), h))) =
    simple f /\ boolean g /\ (h = F_UNTIL (F_BOOL B_TRUE, F_NOT f))) /\
   (simple (F_NOT (F_AND (f,g))) = simple (F_NOT f) /\ simple (F_NOT g)) /\
   (simple (F_NOT f) = boolean f) /\
   (simple (F_AND (f,g)) = simple f /\ simple g) /\
   (simple (F_NEXT f) = simple f) /\
   (simple (F_UNTIL _) = F) /\
   (simple (F_SUFFIX_IMP (r,f)) = S_CLOCK_FREE r /\ simple f) /\
   (simple (F_STRONG_IMP _) = F) /\
   (simple (F_WEAK_IMP _) = F) /\
   (simple (F_ABORT _) = F) /\
   (simple (F_STRONG_CLOCK _) = F)`;

val simple_ind = theorem "simple_ind";

val boolean_simple = store_thm
  ("boolean_simple",
   ``!f. boolean f ==> simple f /\ simple (F_NOT f)``,
   (INDUCT_THEN fl_induct ASSUME_TAC
    >> RW_TAC std_ss [boolean_def, simple_def])
   >> (Cases_on `f` >> RW_TAC std_ss [simple_def])
   >> (Cases_on `f''` >> RW_TAC std_ss [simple_def])
   >> FULL_SIMP_TAC std_ss [boolean_def]);

val UF_SEM_boolean = store_thm
  ("UF_SEM_boolean",
   ``!f p.
       boolean f /\ LENGTH p > 0 ==>
       (UF_SEM (FINITE [ELEM p 0]) f = UF_SEM p f)``,
   INDUCT_THEN fl_induct ASSUME_TAC
   >> RW_TAC std_ss
      [boolean_def, UF_SEM_def, LENGTH, ELEM_def,
       RESTN_def, GT, LENGTH_SEL, LENGTH_def, HEAD_def, HD]);

val boolean_safety_violation = store_thm
  ("boolean_safety_violation",
   ``!p f.
       boolean f /\ IS_INFINITE p ==>
       (safety_violation p f = ~UF_SEM (FINITE [ELEM p 0]) f)``,
   GEN_TAC
   >> Know `!P : num -> (num -> 'a -> bool) -> ('a -> bool) path.
              (!n w. LENGTH (P n w) > 0) ==>
              !f. boolean f ==>
                !n w. ~UF_SEM (P n w) f = ~UF_SEM (FINITE [ELEM (P n w) 0]) f`
   >- (RW_TAC std_ss [] >> PROVE_TAC [UF_SEM_boolean])
   >> DISCH_THEN (MP_TAC o Q.SPEC `\n w. CAT (SEL p (0,n), INFINITE w)`)
   >> MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> (a ==> b) ==> c``)
   >> CONJ_TAC >- RW_TAC std_ss [LENGTH_def, LENGTH_CAT, GT]
   >> BETA_TAC
   >> STRIP_TAC
   >> INDUCT_THEN fl_induct (K ALL_TAC)
   >> RW_TAC std_ss [boolean_def, safety_violation_aux, ELEM_CAT_SEL]);

(* The basic constraint on simple formulas *)

Theorem simple_safety:
   !f p. simple f /\ IS_INFINITE p ==> (safety_violation p f = ~UF_SEM p f)
Proof
   RW_TAC std_ss []
   >> EQ_TAC >- METIS_TAC [safety_violation_refl]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> SIMP_TAC std_ss [AND_IMP_INTRO, GSYM CONJ_ASSOC]
   >> Q.SPEC_TAC (`p`,`p`)
   >> Q.SPEC_TAC (`f`,`f`)
   >> recInduct simple_ind
   >> (REPEAT CONJ_TAC
       >> TRY (ASM_SIMP_TAC std_ss [simple_def, boolean_def] >> NO_TAC)
       >> SIMP_TAC std_ss [boolean_def]
       >> RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `simple X` MP_TAC
       >> ONCE_REWRITE_TAC [simple_def]
       >> RW_TAC std_ss [boolean_def])
   >| [(* F_BOOL *)
       Q.PAT_X_ASSUM `~UF_SEM X Y` MP_TAC
       >> RW_TAC std_ss [simple_def, safety_violation_alt, UF_SEM_def]
       >- METIS_TAC [LENGTH_def, IS_INFINITE_EXISTS, GT]
       >> Q.EXISTS_TAC `1`
       >> RW_TAC bool_ss
            [ONE, SEL_REC_def, CAT_def, ELEM_def, RESTN_def, HEAD_CONS]
       >> PROVE_TAC [ELEM_def, RESTN_def],

       (* F_NOT (F_NOT f) *)
       FULL_SIMP_TAC std_ss [safety_violation_NOT_NOT, UF_SEM_def],

       (* F_NOT (F_AND (F_NOT (F_UNTIL (f,g)), _)) *)
       Q.PAT_X_ASSUM `~UF_SEM X Y` MP_TAC
       >> ASM_SIMP_TAC arith_resq_ss
           [safety_violation_alt, UF_SEM_WEAK_UNTIL, UF_SEM_F_W_ALT,
            xnum_to_def, LENGTH_CAT, LENGTH_IS_INFINITE]
       >> Know `!m n. (m:num) < SUC n = m <= n` >- DECIDE_TAC
       >> DISCH_THEN (fn th => REWRITE_TAC [th])
       >> SIMP_TAC arith_ss [GSYM IMP_DISJ_THM]
       >> RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `!p. X p /\ Y p ==> Z p` (MP_TAC o Q.SPEC `RESTN p j`)
       >> RW_TAC arith_ss
            [IS_INFINITE_RESTN, safety_violation_alt, SEL_REC_RESTN]
       >> Q.EXISTS_TAC `SUC n + j`
       >> RW_TAC std_ss []
       >> Q.EXISTS_TAC `j`
       >> CONJ_TAC
       >- (RW_TAC arith_ss
             [SEL_REC_SPLIT, GSYM CAT_APPEND, RESTN_CAT, LENGTH_SEL_REC]
           >> RW_TAC bool_ss [ADD1]
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_EXISTS, IS_INFINITE_def, IS_INFINITE_CAT])
       >> RW_TAC std_ss []
       >> MP_TAC
          (Q.SPECL [`g`,`RESTN (CAT (SEL_REC (SUC n + j) 0 p,INFINITE w)) k`]
           (GSYM UF_SEM_boolean))
       >> MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
       >> CONJ_TAC
       >- (RW_TAC std_ss []
           >> PROVE_TAC [LENGTH_IS_INFINITE, IS_INFINITE_def,
                         IS_INFINITE_RESTN, IS_INFINITE_CAT, GT])
       >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
       >> Q.PAT_X_ASSUM `!w. P w` (K ALL_TAC)
       >> Q.PAT_X_ASSUM `!w. P w` (MP_TAC o Q.SPEC `k`)
       >> ASM_SIMP_TAC std_ss []
       >> MP_TAC (Q.SPECL [`g`,`RESTN p k`] (GSYM UF_SEM_boolean))
       >> MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
       >> CONJ_TAC
       >- (RW_TAC std_ss []
           >> PROVE_TAC [LENGTH_IS_INFINITE, IS_INFINITE_def,
                         IS_INFINITE_RESTN, IS_INFINITE_CAT, GT])
       >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
       >> MATCH_MP_TAC (PROVE [] ``(a = b) ==> (a ==> b)``)
       >> NTAC 6 (AP_TERM_TAC || AP_THM_TAC)
       >> RW_TAC arith_ss [ELEM_RESTN]
       >> RW_TAC arith_ss [ELEM_def]
       >> Know `k <= j + SUC n` >- DECIDE_TAC
       >> RW_TAC bool_ss [LESS_EQ_EXISTS]
       >> RW_TAC std_ss []
       >> ONCE_REWRITE_TAC [ADD_COMM]
       >> RW_TAC std_ss
            [SEL_REC_SPLIT, GSYM CAT_APPEND, RESTN_CAT, LENGTH_SEL_REC]
       >> RW_TAC arith_ss []
       >> rename [‘j + SUC n = k + p'’]
       >> Cases_on `p'` >- FULL_SIMP_TAC arith_ss []
       >> RW_TAC std_ss [SEL_REC_SUC, CAT_def, HEAD_CONS, ELEM_def],

       (* F_NOT (F_AND (f,g)) *)
       RW_TAC std_ss [safety_violation_def]
       >> Q.PAT_X_ASSUM `~UF_SEM X Y` MP_TAC
       >> ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> ONCE_REWRITE_TAC [GSYM UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> STRIP_TAC
       >> HO_MATCH_MP_TAC
          (METIS_PROVE []
           ``!P Q R.
               (?n. (!q. P n q ==> Q n q) /\ (!q. P n q ==> R n q)) ==>
               ?n. (!q. P n q ==> Q n q /\ R n q)``)
       >> REPEAT (Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `p`))
       >> RW_TAC std_ss [safety_violation_def]
       >> Know `n <= n' \/ n' <= n` >- DECIDE_TAC
       >> RW_TAC std_ss [LESS_EQ_EXISTS]
       >> rename [‘SEL_REC (_ + p')’]
       >| [Q.EXISTS_TAC `n + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT],
           Q.EXISTS_TAC `n' + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT]],

       RW_TAC std_ss [safety_violation_def]
       >> Q.PAT_X_ASSUM `~UF_SEM X Y` MP_TAC
       >> ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> ONCE_REWRITE_TAC [GSYM UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> STRIP_TAC
       >> HO_MATCH_MP_TAC
          (METIS_PROVE []
           ``!P Q R.
               (?n. (!q. P n q ==> Q n q) /\ (!q. P n q ==> R n q)) ==>
               ?n. (!q. P n q ==> Q n q /\ R n q)``)
       >> REPEAT (Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `p`))
       >> RW_TAC std_ss [safety_violation_def]
       >> Know `n <= n' \/ n' <= n` >- DECIDE_TAC
       >> RW_TAC std_ss [LESS_EQ_EXISTS]
       >> rename [‘SEL_REC (_ + p')’]
       >| [Q.EXISTS_TAC `n + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT],
           Q.EXISTS_TAC `n' + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT]],

       RW_TAC std_ss [safety_violation_def]
       >> Q.PAT_X_ASSUM `~UF_SEM X Y` MP_TAC
       >> ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> ONCE_REWRITE_TAC [GSYM UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> STRIP_TAC
       >> HO_MATCH_MP_TAC
          (METIS_PROVE []
           ``!P Q R.
               (?n. (!q. P n q ==> Q n q) /\ (!q. P n q ==> R n q)) ==>
               ?n. (!q. P n q ==> Q n q /\ R n q)``)
       >> REPEAT (Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `p`))
       >> RW_TAC std_ss [safety_violation_def]
       >> Know `n <= n' \/ n' <= n` >- DECIDE_TAC
       >> RW_TAC std_ss [LESS_EQ_EXISTS]
       >> rename [‘SEL_REC (_ + p')’]
       >| [Q.EXISTS_TAC `n + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT],
           Q.EXISTS_TAC `n' + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT]],

       RW_TAC std_ss [safety_violation_def]
       >> Q.PAT_X_ASSUM `~UF_SEM X Y` MP_TAC
       >> ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> ONCE_REWRITE_TAC [GSYM UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> STRIP_TAC
       >> HO_MATCH_MP_TAC
          (METIS_PROVE []
           ``!P Q R.
               (?n. (!q. P n q ==> Q n q) /\ (!q. P n q ==> R n q)) ==>
               ?n. (!q. P n q ==> Q n q /\ R n q)``)
       >> REPEAT (Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `p`))
       >> RW_TAC std_ss [safety_violation_def]
       >> Know `n <= n' \/ n' <= n` >- DECIDE_TAC
       >> RW_TAC std_ss [LESS_EQ_EXISTS]
       >> rename [‘SEL_REC (_ + p')’]
       >| [Q.EXISTS_TAC `n + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT],
           Q.EXISTS_TAC `n' + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT]],

       RW_TAC std_ss [safety_violation_def]
       >> Q.PAT_X_ASSUM `~UF_SEM X Y` MP_TAC
       >> ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> ONCE_REWRITE_TAC [GSYM UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> STRIP_TAC
       >> HO_MATCH_MP_TAC
          (METIS_PROVE []
           ``!P Q R.
               (?n. (!q. P n q ==> Q n q) /\ (!q. P n q ==> R n q)) ==>
               ?n. (!q. P n q ==> Q n q /\ R n q)``)
       >> REPEAT (Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `p`))
       >> RW_TAC std_ss [safety_violation_def]
       >> Know `n <= n' \/ n' <= n` >- DECIDE_TAC
       >> RW_TAC std_ss [LESS_EQ_EXISTS]
       >> rename [‘SEL_REC (_ + p')’]
       >| [Q.EXISTS_TAC `n + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT],
           Q.EXISTS_TAC `n' + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT]],

       RW_TAC std_ss [safety_violation_def]
       >> Q.PAT_X_ASSUM `~UF_SEM X Y` MP_TAC
       >> ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> ONCE_REWRITE_TAC [GSYM UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> STRIP_TAC
       >> HO_MATCH_MP_TAC
          (METIS_PROVE []
           ``!P Q R.
               (?n. (!q. P n q ==> Q n q) /\ (!q. P n q ==> R n q)) ==>
               ?n. (!q. P n q ==> Q n q /\ R n q)``)
       >> REPEAT (Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `p`))
       >> RW_TAC std_ss [safety_violation_def]
       >> Know `n <= n' \/ n' <= n` >- DECIDE_TAC
       >> RW_TAC std_ss [LESS_EQ_EXISTS]
       >> rename [‘SEL_REC (_ + p')’]
       >| [Q.EXISTS_TAC `n + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT],
           Q.EXISTS_TAC `n' + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT]],

       RW_TAC std_ss [safety_violation_def]
       >> Q.PAT_X_ASSUM `~UF_SEM X Y` MP_TAC
       >> ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> ONCE_REWRITE_TAC [GSYM UF_SEM_def]
       >> PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM]
       >> STRIP_TAC
       >> HO_MATCH_MP_TAC
          (METIS_PROVE []
           ``!P Q R.
               (?n. (!q. P n q ==> Q n q) /\ (!q. P n q ==> R n q)) ==>
               ?n. (!q. P n q ==> Q n q /\ R n q)``)
       >> REPEAT (Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `p`))
       >> RW_TAC std_ss [safety_violation_def]
       >> Know `n <= n' \/ n' <= n` >- DECIDE_TAC
       >> RW_TAC std_ss [LESS_EQ_EXISTS]
       >> rename [‘SEL_REC (_ + p')’]
       >| [Q.EXISTS_TAC `n + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT],
           Q.EXISTS_TAC `n' + p'`
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_CAT]],

       (* F_NOT (F_BOOL b) *)
       RW_TAC std_ss [safety_violation_alt]
       >> Q.EXISTS_TAC `1`
       >> POP_ASSUM MP_TAC
       >> RW_TAC bool_ss [ONE, SEL_REC_def, CAT_def, UF_SEM_def]
       >- RW_TAC std_ss [LENGTH_def, CONS_def, GT]
       >> POP_ASSUM MP_TAC
       >> RW_TAC std_ss [ELEM_def, RESTN_def, HEAD_CONS],

       (* F_AND (f,g) *)
       RW_TAC std_ss [safety_violation_alt]
       >> Q.PAT_X_ASSUM `~UF_SEM X Y` MP_TAC
       >> RW_TAC std_ss [UF_SEM_def]
       >| [Q.PAT_X_ASSUM `!p. P p` (K ALL_TAC)
           >> Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `p`)
           >> RW_TAC std_ss [safety_violation_alt]
           >> METIS_TAC [],
           Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `p`)
           >> RW_TAC std_ss [safety_violation_alt]
           >> METIS_TAC []],

       (* F_NEXT f *)
       RW_TAC std_ss [safety_violation_alt]
       >> Q.PAT_X_ASSUM `~UF_SEM X Y` MP_TAC
       >> RW_TAC std_ss [UF_SEM_def]
       >- PROVE_TAC [LENGTH_IS_INFINITE, GT]
       >> Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `RESTN p 1`)
       >> RW_TAC std_ss [safety_violation_alt, IS_INFINITE_RESTN]
       >> Q.EXISTS_TAC `SUC n`
       >> RW_TAC std_ss []
       >> DISJ2_TAC
       >> RW_TAC bool_ss [ONE, SEL_REC_def, CAT_def, RESTN_def, REST_CONS]
       >> METIS_TAC [RESTN_def, ONE],

       (* F_SUFFIX_IMP (r,f) *)
       RW_TAC std_ss [safety_violation_alt]
       >> Q.PAT_X_ASSUM `~UF_SEM X Y` MP_TAC
       >> RW_TAC arith_resq_ss
            [UF_SEM_def, xnum_to_def, LENGTH_CAT, LENGTH_IS_INFINITE, SEL_def]
       >> Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `RESTN p j`)
       >> RW_TAC std_ss [safety_violation_alt, IS_INFINITE_RESTN]
       >> Q.EXISTS_TAC `SUC n + j`
       >> RW_TAC std_ss []
       >> Q.EXISTS_TAC `j`
       >> REVERSE CONJ_TAC
       >- (Q.PAT_X_ASSUM `!w. P w` MP_TAC
           >> RW_TAC arith_ss
                [SEL_REC_SPLIT, RESTN_CAT, LENGTH_SEL_REC, GSYM CAT_APPEND,
                 SEL_REC_RESTN]
           >> RW_TAC std_ss [ADD1]
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC arith_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
           >> METIS_TAC [IS_INFINITE_def, IS_INFINITE_CAT, IS_INFINITE_EXISTS])
       >> Q.PAT_X_ASSUM `US_SEM X Y` MP_TAC
       >> MATCH_MP_TAC (PROVE [] ``(a = b) ==> (a ==> b)``)
       >> AP_THM_TAC
       >> AP_TERM_TAC
       >> Know `SUC n + j = n + (j + 1)` >- DECIDE_TAC
       >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
       >> CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [SEL_REC_SPLIT])))
       >> RW_TAC arith_ss [GSYM CAT_APPEND]
       >> Q.SPEC_TAC (`CAT (SEL_REC n (j + 1) p,INFINITE w)`,`q`)
       >> Q.SPEC_TAC (`p`,`p`)
       >> Q.SPEC_TAC (`j + 1`,`j`)
       >> Induct
       >> RW_TAC std_ss [SEL_REC_def, CAT_def, HEAD_CONS, REST_CONS]
       >> PROVE_TAC []]
QED

(* The regexp checker *)

val bool_checker_def = Define
  `(bool_checker (F_BOOL b) = b) /\
   (bool_checker (F_NOT f) = B_NOT (bool_checker f)) /\
   (bool_checker (F_AND (f,g)) = B_AND (bool_checker f, bool_checker g))`;

val boolean_checker_def = Define
  `boolean_checker f = S_BOOL (bool_checker (F_NOT f))`;

val checker_def = Define
  `(checker (F_BOOL b) = boolean_checker (F_BOOL b)) /\
   (checker (F_NOT (F_NOT f)) = checker f) /\
   (checker (F_NOT (F_AND (F_NOT (F_UNTIL (f,g)), _))) =
    S_CAT
    (S_REPEAT (boolean_checker g),
     S_FLEX_AND (checker f, boolean_checker g))) /\
   (checker (F_NOT (F_AND (f,g))) =
    S_FLEX_AND (checker (F_NOT f), checker (F_NOT g))) /\
   (checker (F_NOT f) = boolean_checker (F_NOT f)) /\
   (checker (F_AND (f,g)) = S_OR (checker f, checker g)) /\
   (checker (F_NEXT f) = S_CAT (S_TRUE, checker f)) /\
   (checker (F_SUFFIX_IMP (r,f)) = S_FUSION (r, checker f))`;

val boolean_checker_CLOCK_FREE = store_thm
  ("boolean_checker_CLOCK_FREE",
   ``!f. boolean f ==> S_CLOCK_FREE (boolean_checker f)``,
   Induct
   >> RW_TAC std_ss [simple_def, S_CLOCK_FREE_def, boolean_checker_def]);

val boolean_checker_initially_ok = store_thm
  ("boolean_checker_initially_ok",
   ``!f. boolean f ==> ~US_SEM [] (boolean_checker f)``,
   recInduct simple_ind
   >> REPEAT CONJ_TAC
   >> RW_TAC arith_ss [boolean_def, boolean_checker_def, bool_checker_def]
   >> ONCE_REWRITE_TAC [US_SEM_def]
   >> RW_TAC arith_ss [listTheory.LENGTH]);

val boolean_checker = store_thm
  ("boolean_checker",
   ``!f p.
       boolean f /\ IS_INFINITE p ==>
       (safety_violation p f =
        ?n. amatch (sere2regexp (boolean_checker f)) (SEL p (0,n)))``,
   SIMP_TAC arith_ss
     [amatch, GSYM sere2regexp, boolean_checker_CLOCK_FREE,
      boolean_safety_violation, boolean_checker_def, bool_checker_def,
      US_SEM_def, B_SEM, UF_SEM_def, LENGTH_SEL, ELEM_SEL]
   >> INDUCT_THEN fl_induct ASSUME_TAC
   >> REPEAT (POP_ASSUM MP_TAC)
   >> SIMP_TAC arith_ss
      [boolean_def, bool_checker_def, UF_SEM_def, LENGTH_def, HD,
       ELEM_def, GT, B_SEM_def, RESTN_def, HEAD_def, listTheory.LENGTH]);

val boolean_checker_SEL_REC = store_thm
  ("boolean_checker_SEL_REC",
   ``!f p.
       boolean f /\ IS_INFINITE p ==>
       (safety_violation p f =
        ?n. amatch (sere2regexp (boolean_checker f)) (SEL_REC n 0 p))``,
   RW_TAC arith_ss
     [boolean_checker, SEL_def, amatch, GSYM sere2regexp,
      boolean_checker_CLOCK_FREE]
   >> EQ_TAC >- PROVE_TAC []
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> REVERSE (Cases_on `n`) >- PROVE_TAC [ADD1]
   >> RW_TAC std_ss [SEL_REC_def, boolean_checker_initially_ok]);

val boolean_checker_US_SEM = store_thm
  ("boolean_checker_US_SEM",
   ``!f p.
       boolean f /\ IS_INFINITE p ==>
       (safety_violation p f =
        ?n. US_SEM (SEL_REC n 0 p) (boolean_checker f))``,
   SIMP_TAC std_ss
     [boolean_checker_SEL_REC, amatch, GSYM sere2regexp,
      boolean_checker_CLOCK_FREE]);

val US_SEM_boolean_checker = store_thm
  ("US_SEM_boolean_checker",
   ``!f w.
       US_SEM w (boolean_checker f) =
       (?x. (w = [x]) /\ US_SEM [x] (boolean_checker f))``,
   RW_TAC std_ss [US_SEM_def, boolean_checker_def]
   >> Cases_on `w` >- RW_TAC std_ss [LENGTH]
   >> REVERSE (Cases_on `t`) >- RW_TAC bool_ss [LENGTH, ONE]
   >> RW_TAC std_ss []);

val US_SEM_boolean_checker_SEL_REC = store_thm
  ("US_SEM_boolean_checker_SEL_REC",
   ``!f n m p.
       US_SEM (SEL_REC n m p) (boolean_checker f) =
       (n = 1) /\ US_SEM (SEL_REC 1 m p) (boolean_checker f)``,
   RW_TAC std_ss []
   >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [US_SEM_boolean_checker]))
   >> Cases_on `n` >- RW_TAC std_ss [SEL_REC_def]
   >> EQ_TAC
   >| [STRIP_TAC
       >> MATCH_MP_TAC (PROVE [] ``(a ==> b) /\ a ==> a /\ b``)
       >> CONJ_TAC >- PROVE_TAC []
       >> METIS_TAC [LENGTH_SEL_REC, ONE, LENGTH],
       RW_TAC bool_ss [ONE]
       >> Cases_on `SEL_REC (SUC 0) m p`
       >- PROVE_TAC [LENGTH_SEL_REC, LENGTH, numTheory.NOT_SUC]
       >> Suff `t = []` >- PROVE_TAC []
       >> Cases_on `t` >- RW_TAC std_ss []
       >> PROVE_TAC [LENGTH_SEL_REC, LENGTH, numTheory.NOT_SUC,
                     prim_recTheory.INV_SUC_EQ]]);

val US_SEM_boolean_checker_CONJ = store_thm
  ("US_SEM_boolean_checker_CONJ",
   ``!f p.
       (?w. US_SEM w (boolean_checker f) /\ p w f) =
       (?x. US_SEM [x] (boolean_checker f) /\ p [x] f)``,
   RW_TAC std_ss [US_SEM_def, boolean_checker_def]
   >> MATCH_MP_TAC EQ_SYM
   >> MP_TAC
      (PROVE [list_CASES]
       ``!p q. (q = p [] \/ ?t (h : 'a -> bool). p (h::t)) ==> (q = ?l. p l)``)
   >> DISCH_THEN (fn th => HO_MATCH_MP_TAC th >> ASSUME_TAC th)
   >> SIMP_TAC std_ss [LENGTH]
   >> POP_ASSUM HO_MATCH_MP_TAC
   >> RW_TAC arith_ss [LENGTH]);

val boolean_checker_US_SEM1 = store_thm
  ("boolean_checker_US_SEM1",
   ``!f p.
       boolean f /\ IS_INFINITE p ==>
       (US_SEM (SEL_REC 1 0 p) (boolean_checker f) = ~UF_SEM p f)``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`f`, `p`] (GSYM boolean_checker_US_SEM))
   >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [US_SEM_boolean_checker_SEL_REC]))
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [simple_safety, boolean_simple]);

val checker_initially_ok = store_thm
  ("checker_initially_ok",
   ``!f. simple f ==> ~US_SEM [] (checker f)``,
   recInduct simple_ind
   >> REPEAT CONJ_TAC
   >> RW_TAC arith_ss [simple_def, checker_def, boolean_checker_def,
                       bool_checker_def]
   >> ONCE_REWRITE_TAC [US_SEM_def]
   >> ONCE_REWRITE_TAC [US_SEM_def]
   >> RW_TAC arith_ss [listTheory.LENGTH, US_SEM_REPEAT_TRUE,
                       listTheory.APPEND_eq_NIL, S_FLEX_AND_EMPTY]
   >> RW_TAC std_ss [US_SEM_def, S_TRUE_def, LENGTH]);

val checker_CLOCK_FREE = store_thm
  ("checker_CLOCK_FREE",
   ``!f. simple f ==> S_CLOCK_FREE (checker f)``,
   recInduct simple_ind
   >> REPEAT CONJ_TAC
   >> RW_TAC std_ss [simple_def, S_CLOCK_FREE_def, checker_def, S_TRUE_def,
                     boolean_checker_CLOCK_FREE, S_FLEX_AND_def, S_FALSE_def]
   >> PROVE_TAC [boolean_def, boolean_checker_CLOCK_FREE]);

Theorem checker_NOT_AND:
   !f g.
       (!p.
          simple (F_NOT f) /\ IS_INFINITE p ==>
          (safety_violation p (F_NOT f) =
           ?n. US_SEM (SEL_REC n 0 p) (checker (F_NOT f)))) /\
       (!p.
          simple (F_NOT g) /\ IS_INFINITE p ==>
          (safety_violation p (F_NOT g) =
           ?n. US_SEM (SEL_REC n 0 p) (checker (F_NOT g)))) ==>
       !p.
         (simple (F_NOT f) /\ simple (F_NOT g)) /\ IS_INFINITE p ==>
         (safety_violation p (F_NOT (F_AND (f,g))) =
          ?n.
            US_SEM (SEL_REC n 0 p)
              (S_FLEX_AND (checker (F_NOT f),checker (F_NOT g))))
Proof
   RW_TAC std_ss [safety_violation_alt, UF_SEM_def, S_FLEX_AND]
   >> REPEAT (Q.PAT_X_ASSUM `!x. P x` (fn th => RW_TAC std_ss [GSYM th]))
   >> EQ_TAC >- PROVE_TAC []
   >> RW_TAC std_ss []
   >> Know `n <= n' \/ n' <= n` >- DECIDE_TAC
   >> RW_TAC std_ss [LESS_EQ_EXISTS]
   >> rename [‘SEL_REC (_ + p')’]
   >| [Q.EXISTS_TAC `n + p'`
       >> RW_TAC std_ss []
       >> ONCE_REWRITE_TAC [ADD_COMM]
       >> RW_TAC arith_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
       >> PROVE_TAC [IS_INFINITE_CAT, IS_INFINITE_EXISTS],
       Q.EXISTS_TAC `n' + p'`
       >> RW_TAC std_ss []
       >> ONCE_REWRITE_TAC [ADD_COMM]
       >> RW_TAC arith_ss [SEL_REC_SPLIT, GSYM CAT_APPEND]
       >> PROVE_TAC [IS_INFINITE_CAT, IS_INFINITE_EXISTS]]
QED

val checker_AND = store_thm
  ("checker_AND",
   ``!f g.
       (!p.
          simple f /\ IS_INFINITE p ==>
          (safety_violation p f =
           ?n. US_SEM (SEL_REC n 0 p) (checker f))) /\
       (!p.
          simple g /\ IS_INFINITE p ==>
          (safety_violation p g =
           ?n. US_SEM (SEL_REC n 0 p) (checker g))) ==>
       !p.
         (simple f /\ simple g) /\ IS_INFINITE p ==>
         (safety_violation p (F_AND (f,g)) =
          ?n. US_SEM (SEL_REC n 0 p) (S_OR (checker f,checker g)))``,
   RW_TAC std_ss [simple_safety, simple_def, UF_SEM_def, US_SEM_def]
   >> METIS_TAC []);

val checker_NEXT = store_thm
  ("checker_NEXT",
   ``!f.
      (!p.
         simple f /\ IS_INFINITE p ==>
         (safety_violation p f =
          ?n. US_SEM (SEL_REC n 0 p) (checker f))) ==>
      !p.
        simple f /\ IS_INFINITE p ==>
        (safety_violation p (F_NEXT f) =
         ?n. US_SEM (SEL_REC n 0 p) (S_CAT (S_TRUE,checker f)))``,
   RW_TAC std_ss []
   >> RW_TAC arith_suc_ss
        [safety_violation_alt, UF_SEM_def, US_SEM_def, LENGTH_CAT,
         S_TRUE_def, GT, B_SEM, RESTN_def, REST_CAT, SEL_NIL]
   >> Know `!P Q. (P 0 \/ (?n. P (SUC n)) = Q) ==> ((?n. P n) = Q)`
   >- PROVE_TAC [arithmeticTheory.num_CASES]
   >> DISCH_THEN HO_MATCH_MP_TAC
   >> RW_TAC std_ss [SEL_REC_def, CAT_def, REST_CONS]
   >> MATCH_MP_TAC (PROVE [] ``(a ==> b) /\ (b = c) ==> (a \/ b = c)``)
   >> CONJ_TAC
   >- (RW_TAC std_ss []
       >> Q.EXISTS_TAC `0`
       >> RW_TAC std_ss [SEL_REC_def, CAT_def]
       >> Know `!q. IS_INFINITE q ==> ~UF_SEM (REST q) f`
       >- PROVE_TAC [IS_INFINITE_def, path_nchotomy]
       >> DISCH_THEN (MP_TAC o Q.SPEC `CONS (x, INFINITE w)`)
       >> RW_TAC std_ss [REST_CONS, IS_INFINITE_CONS, IS_INFINITE_def])
   >> RW_TAC std_ss [GSYM safety_violation_alt, IS_INFINITE_REST]
   >> Know `!P Q. (P = (?n. Q n []) \/ (?n h. Q n [h]) \/
                   (?h1 h2 t n. Q n (h1 :: h2 :: t))) ==>
                  (P = ?n w1. Q (n : num) (w1 : ('a -> bool) list))`
   >- metisLib.METIS_TAC [list_CASES]
   >> DISCH_THEN HO_MATCH_MP_TAC
   >> RW_TAC arith_suc_ss [LENGTH, APPEND]
   >> Know `!P Q. (?h w2. P h (w2 : ('a -> bool) list) /\ Q w2) =
                  ?w2. (?h : 'a -> bool. P h w2) /\ Q w2`
   >- PROVE_TAC []
   >> DISCH_THEN (fn th => SIMP_TAC std_ss [th])
   >> Know `!P Q. (Q = P 0 \/ ?n. P (SUC n)) ==> (Q = ?n. P n)`
   >- PROVE_TAC [arithmeticTheory.num_CASES]
   >> DISCH_THEN HO_MATCH_MP_TAC
   >> RW_TAC arith_suc_ss [SEL_REC_def, TL, checker_initially_ok]);

val checker_UNTIL = store_thm
  ("checker_UNTIL",
   ``!f g h.
       (!p.
          simple f /\ IS_INFINITE p ==>
          (safety_violation p f =
           ?n. US_SEM (SEL_REC n 0 p) (checker f))) ==>
       !p.
         (simple f /\ boolean g /\
          (h = F_UNTIL (F_BOOL B_TRUE,F_NOT f))) /\ IS_INFINITE p ==>
         (safety_violation p (F_NOT (F_AND (F_NOT (F_UNTIL (f,g)),h))) =
          ?n.
            US_SEM (SEL_REC n 0 p)
              (S_CAT
                 (S_REPEAT (boolean_checker g),
                  S_FLEX_AND (checker f,boolean_checker g))))``,
   RW_TAC std_ss []
   >> Know
      `safety_violation p
       (F_NOT (F_AND (F_NOT (F_UNTIL (f,g)),F_UNTIL (F_BOOL B_TRUE,F_NOT f)))) =
       safety_violation p (F_W (f,g))`
   >- (RW_TAC std_ss
       [safety_violation_def, UF_SEM_def, F_W_def, F_OR_def, F_G_def, F_F_def])
   >> DISCH_THEN (fn th => SIMP_TAC std_ss [th])
   >> RW_TAC arith_resq_ss
        [safety_violation_alt, UF_SEM_F_W_ALT, LENGTH_CAT, S_TRUE_def]
   >> Know `!m n. (m:num) < SUC n = m <= n` >- DECIDE_TAC
   >> DISCH_THEN (fn th => REWRITE_TAC [th])
   >> SIMP_TAC arith_ss [GSYM IMP_DISJ_THM]
   >> REVERSE EQ_TAC
   >- (RW_TAC std_ss [S_CAT_SEL_REC, S_FLEX_AND]
       >> Q.EXISTS_TAC `m + n`
       >> POP_ASSUM MP_TAC
       >> ONCE_REWRITE_TAC [US_SEM_boolean_checker_SEL_REC]
       >> RW_TAC std_ss [RESTN_RESTN]
       >> Q.EXISTS_TAC `m`
       >> CONJ_TAC
       >- (ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC arith_ss
                [SEL_REC_SPLIT, LENGTH_SEL_REC, RESTN_CAT, GSYM CAT_APPEND]
           >> Know `m = 0 + m` >- DECIDE_TAC
           >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
           >> RW_TAC std_ss [GSYM SEL_REC_RESTN]
           >> MATCH_MP_TAC safety_violation_refl
           >> RW_TAC std_ss
                [IS_INFINITE_CAT, IS_INFINITE_def, IS_INFINITE_RESTN]
           >> Q.EXISTS_TAC `n`
           >> RW_TAC std_ss [SEL_REC_CAT_0, LENGTH_SEL_REC])
       >> RW_TAC std_ss []
       >> STRIP_TAC
       >> Q.PAT_X_ASSUM `k <= m` MP_TAC
       >> Suff `~(k = m) /\ m <= k` >- DECIDE_TAC
       >> CONJ_TAC
       >- (STRIP_TAC
           >> RW_TAC arith_ss []
           >> POP_ASSUM MP_TAC
           >> RW_TAC std_ss []
           >> MATCH_MP_TAC safety_violation_refl
           >> RW_TAC std_ss
                [IS_INFINITE_RESTN, IS_INFINITE_CAT, IS_INFINITE_def,
                 boolean_checker_US_SEM]
           >> Q.EXISTS_TAC `1`
           >> POP_ASSUM MP_TAC
           >> MATCH_MP_TAC (PROVE [] ``(a = b) ==> (a ==> b)``)
           >> AP_THM_TAC
           >> AP_TERM_TAC
           >> RW_TAC arith_ss [SEL_REC_RESTN]
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC arith_ss
                [SEL_REC_SPLIT, GSYM CAT_APPEND, SEL_REC_CAT, LENGTH_SEL_REC]
           >> Know `~(n = 0)` >- PROVE_TAC [checker_initially_ok, SEL_REC_def]
           >> STRIP_TAC
           >> Know `1 <= n` >- DECIDE_TAC
           >> RW_TAC std_ss [LESS_EQ_EXISTS]
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC std_ss
                [SEL_REC_SPLIT, GSYM CAT_APPEND, SEL_REC_CAT_0, LENGTH_SEL_REC])
       >> Q.PAT_X_ASSUM `UF_SEM X Y` MP_TAC
       >> Q.PAT_X_ASSUM `US_SEM X (S_REPEAT Y)` MP_TAC
       >> Q.PAT_X_ASSUM `IS_INFINITE p` MP_TAC
       >> Q.SPEC_TAC (`p`,`p`)
       >> Q.SPEC_TAC (`k`,`k`)
       >> Q.SPEC_TAC (`m`,`m`)
       >> Q.PAT_X_ASSUM `boolean g` MP_TAC
       >> POP_ASSUM_LIST (K ALL_TAC)
       >> STRIP_TAC
       >> SIMP_TAC std_ss [AND_IMP_INTRO]
       >> Induct
       >> RW_TAC arith_ss []
       >> Q.PAT_X_ASSUM `US_SEM X Y` MP_TAC
       >> ONCE_REWRITE_TAC [GSYM S_REPEAT_UNWIND]
       >> ONCE_REWRITE_TAC [US_SEM_def]
       >> SIMP_TAC std_ss [S_EMPTY, S_CAT_SEL_REC0]
       >> STRIP_TAC >- PROVE_TAC [LENGTH_SEL_REC, LENGTH, numTheory.NOT_SUC]
       >> REPEAT (Q.PAT_X_ASSUM `US_SEM X Y` MP_TAC)
       >> ONCE_REWRITE_TAC [US_SEM_boolean_checker_SEL_REC]
       >> RW_TAC arith_ss []
       >> Cases_on `k`
       >- (RW_TAC arith_ss []
           >> Q.PAT_X_ASSUM `!k. P k` (K ALL_TAC)
           >> Q.PAT_X_ASSUM `UF_SEM X Y` MP_TAC
           >> RW_TAC std_ss [RESTN_def]
           >> MATCH_MP_TAC safety_violation_refl
           >> RW_TAC std_ss
                [IS_INFINITE_RESTN, IS_INFINITE_CAT, IS_INFINITE_def,
                 boolean_checker_US_SEM]
           >> Q.EXISTS_TAC `1`
           >> Know `n + SUC m = (n + m) + 1` >- DECIDE_TAC
           >> DISCH_THEN (fn th => REWRITE_TAC [th])
           >> ONCE_REWRITE_TAC [SEL_REC_SPLIT]
           >> RW_TAC std_ss [GSYM CAT_APPEND, SEL_REC_CAT_0, LENGTH_SEL_REC])
       >> RW_TAC arith_ss []
       >> FIRST_ASSUM MATCH_MP_TAC
       >> Q.EXISTS_TAC `REST p`
       >> POP_ASSUM MP_TAC
       >> RW_TAC bool_ss [IS_INFINITE_REST, ONE, RESTN_def]
       >> Q.PAT_X_ASSUM `UF_SEM X Y` MP_TAC
       >> MATCH_MP_TAC (PROVE [] ``(a = b) ==> (a ==> b)``)
       >> AP_THM_TAC
       >> AP_TERM_TAC
       >> RW_TAC std_ss [RESTN_def, ADD_CLAUSES, SEL_REC_def, REST_CAT, TL]
       >> PROVE_TAC [ADD_COMM])
   >> STRIP_TAC
   >> RW_TAC std_ss [S_CAT_SEL_REC, S_FLEX_AND]
   >> ONCE_REWRITE_TAC [US_SEM_boolean_checker_SEL_REC]
   >> RW_TAC std_ss []
   >> Know `?w. INFINITE w = RESTN p n`
   >- METIS_TAC [IS_INFINITE_EXISTS, IS_INFINITE_RESTN]
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `!w. P w` (MP_TAC o Q.SPEC `w`)
   >> RW_TAC std_ss [CAT_SEL_REC_RESTN]
   >> Q.PAT_X_ASSUM `INFINITE w = x` (K ALL_TAC)
   >> Q.PAT_X_ASSUM `!p : ('a -> bool) path. P p` (MP_TAC o Q.SPEC `RESTN p j`)
   >> RW_TAC std_ss [IS_INFINITE_RESTN, simple_safety]
   >> Q.EXISTS_TAC `j`
   >> REVERSE CONJ_TAC
   >- (CONJ_TAC >- METIS_TAC []
       >> RW_TAC std_ss [boolean_checker_US_SEM1, IS_INFINITE_RESTN]
       >> PROVE_TAC [LESS_EQ_REFL])
   >> Know `j = j + 0` >- DECIDE_TAC
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   >> Know `p = RESTN p (j - (j + 0))` >- RW_TAC arith_ss [RESTN_def]
   >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   >> Know `j + 0 <= j` >- DECIDE_TAC
   >> Q.SPEC_TAC (`j + 0`, `k`)
   >> Induct
   >- (RW_TAC std_ss [SEL_REC_def, US_SEM_def]
       >> METIS_TAC [CONCAT_def, EVERY_DEF])
   >> ONCE_REWRITE_TAC [GSYM S_REPEAT_UNWIND]
   >> ONCE_REWRITE_TAC [US_SEM_def]
   >> ONCE_REWRITE_TAC [US_SEM_def]
   >> RW_TAC std_ss []
   >> DISJ2_TAC
   >> RW_TAC std_ss [ADD1, SEL_REC_SPLIT]
   >> Q.PAT_X_ASSUM `X ==> Y` MP_TAC
   >> (MP_TAC o Q.SPEC `k` o GENL [``m:num``,``n:num``,``r:num``] o
       INST_TYPE [alpha |-> ``:'a -> bool``]) SEL_REC_RESTN
   >> RW_TAC arith_ss []
   >> Q.EXISTS_TAC `SEL_REC 1 0 (RESTN p (j - (k + 1)))`
   >> Q.EXISTS_TAC `SEL_REC k (j - k) p`
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [boolean_checker_US_SEM1, IS_INFINITE_RESTN]
   >> FIRST_ASSUM MATCH_MP_TAC
   >> DECIDE_TAC);

val checker_SEL_REC = store_thm
  ("checker_SEL_REC",
   ``!f p.
       simple f /\ IS_INFINITE p ==>
       (safety_violation p f =
        ?n. amatch (sere2regexp (checker f)) (SEL_REC n 0 p))``,
   SIMP_TAC std_ss [amatch, GSYM sere2regexp, checker_CLOCK_FREE]
   >> recInduct simple_ind
   >> (REPEAT CONJ_TAC
       >> TRY (ASM_SIMP_TAC std_ss [simple_def, boolean_def] >> NO_TAC)
       >> SIMP_TAC std_ss [boolean_def])
   >| [(* F_BOOL *)
       RW_TAC std_ss [boolean_checker_US_SEM, boolean_def, checker_def],

       (* F_NOT (F_NOT f) *)
       RW_TAC std_ss [safety_violation_def, UF_SEM_def, simple_def, checker_def]
       >> RW_TAC std_ss [GSYM safety_violation_def],

       (* F_NOT (F_AND (F_NOT (F_UNTIL (f,g)), _)) *)
       ONCE_REWRITE_TAC [simple_def, checker_def]
       >> METIS_TAC [checker_UNTIL],

       (* F_NOT (F_AND (f,g)) *)
       RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `simple X` MP_TAC
       >> ONCE_REWRITE_TAC [simple_def, checker_def]
       >> RW_TAC std_ss [boolean_def]
       >> METIS_TAC [checker_NOT_AND],
       RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `simple X` MP_TAC
       >> ONCE_REWRITE_TAC [simple_def, checker_def]
       >> RW_TAC std_ss [boolean_def]
       >> METIS_TAC [checker_NOT_AND],
       RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `simple X` MP_TAC
       >> ONCE_REWRITE_TAC [simple_def, checker_def]
       >> RW_TAC std_ss [boolean_def]
       >> METIS_TAC [checker_NOT_AND],
       RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `simple X` MP_TAC
       >> ONCE_REWRITE_TAC [simple_def, checker_def]
       >> RW_TAC std_ss [boolean_def]
       >> METIS_TAC [checker_NOT_AND],
       RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `simple X` MP_TAC
       >> ONCE_REWRITE_TAC [simple_def, checker_def]
       >> RW_TAC std_ss [boolean_def]
       >> METIS_TAC [checker_NOT_AND],
       RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `simple X` MP_TAC
       >> ONCE_REWRITE_TAC [simple_def, checker_def]
       >> RW_TAC std_ss [boolean_def]
       >> METIS_TAC [checker_NOT_AND],
       RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `simple X` MP_TAC
       >> ONCE_REWRITE_TAC [simple_def, checker_def]
       >> RW_TAC std_ss [boolean_def]
       >> METIS_TAC [checker_NOT_AND],

       (* F_NOT (F_BOOL b) *)
       RW_TAC std_ss
         [boolean_checker_US_SEM, boolean_def, simple_def, checker_def],

       (* F_AND (f,g) *)
       ONCE_REWRITE_TAC [simple_def, checker_def]
       >> METIS_TAC [checker_AND],

       (* F_NEXT f *)
       ONCE_REWRITE_TAC [simple_def, checker_def]
       >> METIS_TAC [checker_NEXT],

       (* F_SUFFIX_IMP (r,f) *)
       RW_TAC arith_resq_ss
         [simple_def, checker_def, simple_safety, UF_SEM_def,
          LENGTH_IS_INFINITE, SEL_def, IS_INFINITE_RESTN, S_FUSION_SEL_REC]
       >> REVERSE EQ_TAC >- METIS_TAC []
       >> RW_TAC std_ss []
       >> REVERSE (Cases_on `n`) >- METIS_TAC [ADD1]
       >> METIS_TAC [SEL_REC_def, checker_initially_ok]]);

val checker = store_thm
  ("checker",
   ``!f p.
       simple f /\ IS_INFINITE p ==>
       (safety_violation p f =
        ?n. amatch (sere2regexp (checker f)) (SEL p (0,n)))``,
   RW_TAC arith_ss [checker_SEL_REC, SEL_def]
   >> REVERSE EQ_TAC >- METIS_TAC []
   >> RW_TAC std_ss [amatch, GSYM sere2regexp, checker_CLOCK_FREE]
   >> REVERSE (Cases_on `n`) >- METIS_TAC [ADD1]
   >> METIS_TAC [SEL_REC_def, checker_initially_ok]);

(******************************************************************************
* Beginning of some stuff that turned out to be useless for execution.
* Leaving it here as just conceivably a future use might appear!
******************************************************************************)

(******************************************************************************
* Formula version of an operator due to Dana Fisman
******************************************************************************)
val F_PREF_def =
 pureDefine `F_PREF w f = ?w'. UF_SEM (CAT(w,w')) f`;

val EXISTS_RES_to =
 store_thm
  ("EXISTS_RES_to",
   ``!m n P.
      (?j :: (m to n). P j n) =  (m < n) /\ (P m n \/ ?j :: ((m+1) to n). P j n)``,
   Cases_on `n`
    THEN RW_TAC std_resq_ss [num_to_def,xnum_to_def,LS]
    THENL
     [PROVE_TAC[DECIDE ``m <= j = (m=j) \/ m+1 <= j``],
      EQ_TAC
       THEN RW_TAC std_ss []
       THEN TRY(PROVE_TAC[DECIDE ``m <= j = (m=j) \/ m+1 <= j``])
       THEN DECIDE_TAC]);

val ABORT_AUX_def =
 pureDefine
  `ABORT_AUX w f b n =
    ?(j::n to LENGTH w).
      UF_SEM (RESTN w j) (F_BOOL b) /\ F_PREF (SEL w (0,j - 1)) f`;

val EXISTS_RES_to_COR =
 SIMP_RULE std_ss []
  (Q.SPECL
    [`n`,`LENGTH(w :('a -> bool) path)`,
     `\j n. UF_SEM (RESTN w j) (F_BOOL b) /\ F_PREF (SEL w (0,j - 1)) f`]
    EXISTS_RES_to);

val ABORT_AUX_REC =
 store_thm
  ("ABORT_AUX_REC",
   ``ABORT_AUX w f b n
      = n < LENGTH w /\
        (UF_SEM (RESTN w n) (F_BOOL b) /\ F_PREF (SEL w (0,n - 1)) f
         \/
         ABORT_AUX w f b (n+1))``,
   RW_TAC std_ss [ABORT_AUX_def]
    THEN ACCEPT_TAC EXISTS_RES_to_COR);

val UF_ABORT_REC =
 store_thm
  ("UF_ABORT_REC",
   ``UF_SEM w (F_ABORT (f,b)) =
      UF_SEM w f \/ UF_SEM w (F_BOOL b) \/ ABORT_AUX w f b 1``,
     RW_TAC std_resq_ss [UF_SEM_def,F_PREF_def,ABORT_AUX_def]
    THEN PROVE_TAC[]);

(******************************************************************************
* End of useless stuff.
******************************************************************************)


val _ = export_theory();
