(*****************************************************************************)
(* Correctness of the PSL 1.1 rewrites                                       *)
(* (guided in some places by hand proofs due to Dana Fisman)                 *)
(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* Started:   Wed Feb 25, 2004                                               *)
(* Completed: Sat Mar 06, 2004                                               *)
(*****************************************************************************)

Theory RewritesProperties
Ancestors
  FinitePSLPath PSLPath Syntax SyntacticSugar UnclockedSemantics
  ClockedSemantics Rewrites arithmetic list rich_list res_quan
  ClockedSemantics Lemmas FinitePSLPath PSLPath
Libs
  res_quanLib

val _ = ParseExtras.temp_loose_equality()

local
  val th = prove (``!a b. a /\ (a ==> b) ==> a /\ b``, PROVE_TAC [])
in
  val STRONG_CONJ_TAC :tactic = MATCH_MP_TAC th >> CONJ_TAC
end;

(******************************************************************************
* A simpset fragment to rewrite away quantifiers restricted with :: (a to b)
******************************************************************************)
val resq_SS =
 simpLib.merge_ss
  [res_quanTools.resq_SS,
   rewrites
    [IN_DEF,LESS_def,LESSX_def,LENGTH_def]];

(* SEREs only need finite paths *)
open FinitePSLPathTheory;

Theorem US_SEM_BOOL_REWRITE_LEMMA:
     US_SEM v (S_CAT (S_REPEAT (S_BOOL (B_NOT c)),S_BOOL (B_AND (c,b)))) =
      LENGTH v > 0 /\
      B_SEM (ELEM v (LENGTH v - 1)) b /\
      B_SEM (ELEM v (LENGTH v - 1)) c /\
      !i. i < LENGTH v - 1 ==> B_SEM (ELEM v i) (B_NOT c)
Proof
   RW_TAC  (std_ss++resq_SS) [US_SEM_def,LENGTH1]
    THEN EQ_TAC
    THEN RW_TAC list_ss [LENGTH_APPEND]
    THEN FULL_SIMP_TAC list_ss
          [ELEM_def,RESTN_def,HEAD_def,B_SEM_def,LENGTH_APPEND,RESTN_APPEND]
    THENL
     [Cases_on `x`
       THEN FULL_SIMP_TAC list_ss [B_SEM_def],
      Cases_on `x`
       THEN FULL_SIMP_TAC list_ss [B_SEM_def],
      FULL_SIMP_TAC list_ss [EVERY_EL,EL_APPEND1,HD_RESTN]
       THEN `(LENGTH (CONCAT vlist) = LENGTH vlist) /\ i < LENGTH vlist`
            by PROVE_TAC[EVERY_EL_SINGLETON_LENGTH]
       THEN `CONCAT vlist = MAP HD vlist` by  PROVE_TAC[EVERY_EL_SINGLETON]
       THEN RW_TAC list_ss [EL_MAP]
       THEN PROVE_TAC[HD],
      FULL_SIMP_TAC list_ss [EVERY_EL,EL_APPEND1,HD_RESTN]
       THEN Q.EXISTS_TAC `BUTLAST v`
       THEN Q.EXISTS_TAC `[LAST v]`
       THEN RW_TAC list_ss []
       THEN RW_TAC list_ss [APPEND_BUTLAST_LAST,LENGTH_NIL_LEMMA]
       THEN `LENGTH v >= 1` by DECIDE_TAC
       THENL
        [Q.EXISTS_TAC `MAP(\l.[l])(BUTLAST v)`
          THEN RW_TAC list_ss [CONCAT_MAP_SINGLETON,EL_MAP]
          THEN IMP_RES_TAC LENGTH_NIL_LEMMA
          THEN IMP_RES_TAC LENGTH_BUTLAST
          THEN `n:num < LENGTH v - 1` by DECIDE_TAC
          THEN PROVE_TAC[EL_BUTLAST],
         IMP_RES_TAC EL_PRE_LENGTH
          THEN POP_ASSUM(fn th => RW_TAC list_ss [GSYM th])
          THEN Cases_on `EL (LENGTH v - 1) v`
          THEN FULL_SIMP_TAC std_ss [B_SEM_def]]]
QED

(******************************************************************************
* v |=c r  <==>  v |= (S_CLOCK_COMP c r)
******************************************************************************)

Theorem S_CLOCK_COMP_CORRECT:
     !r v c. S_SEM v c r = US_SEM v (S_CLOCK_COMP c r)
Proof
   INDUCT_THEN sere_induct ASSUME_TAC
    THENL
     [(* S_BOOL b *)
      RW_TAC std_ss [S_SEM_def, US_SEM_def]
       THEN RW_TAC std_ss [CLOCK_TICK_def]
       THEN RW_TAC (std_ss++resq_SS) []
       THEN RW_TAC (std_ss++resq_SS) [S_CLOCK_COMP_def]
       THEN PROVE_TAC[US_SEM_BOOL_REWRITE_LEMMA],
      (* S_CAT(r,r') *)
      RW_TAC (std_ss ++ resq_SS) [S_SEM_def, US_SEM_def, S_CLOCK_COMP_def],
      (* S_FUSION (r,r') *)
      RW_TAC (std_ss ++ resq_SS) [S_SEM_def, US_SEM_def, S_CLOCK_COMP_def],
      (* S_OR (r,r') *)
      RW_TAC (std_ss ++ resq_SS) [S_SEM_def, US_SEM_def, S_CLOCK_COMP_def],
      (* S_AND (r,r') *)
      RW_TAC (std_ss ++ resq_SS) [S_SEM_def, US_SEM_def, S_CLOCK_COMP_def],
      (* S_EMPTY *)
      RW_TAC (std_ss ++ resq_SS) [S_SEM_def, US_SEM_def, S_CLOCK_COMP_def],
      (* S_REPEAT r *)
      RW_TAC (std_ss ++ resq_SS) [S_SEM_def, US_SEM_def, S_CLOCK_COMP_def],
      (* S_CLOCK (r,p_2) *)
      RW_TAC (std_ss ++ resq_SS) [S_SEM_def, US_SEM_def, S_CLOCK_COMP_def]]
QED

(******************************************************************************
* Structural induction rule for FL formulas
******************************************************************************)
(* Formulas need infinite paths *)
open PSLPathTheory;

val fl_induct =
 save_thm
  ("fl_induct",
   Q.GEN
    `P`
    (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2 /\ B3)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\ (f,b). P f`,`\ (r,f). P f`,`\ (f1,f2). P f1 /\ P f2`]
         (TypeBase.induction_of ``:'a fl``)))));

Theorem LS_LE_X:
     m:num < n:xnum ==> m <= n
Proof
   Cases_on `n`
    THEN RW_TAC arith_ss [LS,LE]
QED

Theorem LS_TRANS_X:
     m:num < n:num ==> n < p:xnum ==> m < p
Proof
   Cases_on `p`
    THEN RW_TAC arith_ss [LS]
QED

local
open FinitePSLPathTheory
in
Theorem RESTN_NIL_LENGTH:
     !k v. k <= LENGTH v ==> ((RESTN v k = []) = (LENGTH v = k))
Proof
   Induct
    THEN RW_TAC list_ss [FinitePSLPathTheory.RESTN_def,LENGTH_NIL,REST_def]
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(Q.SPEC `TL v` (el 2 thl)))
    THEN `0 < LENGTH v` by DECIDE_TAC
    THEN `LENGTH(TL v) = LENGTH v - 1` by PROVE_TAC[LENGTH_TL]
    THEN `k <= LENGTH(TL v)` by DECIDE_TAC
    THEN RES_TAC
    THEN RW_TAC list_ss []
QED
end;

Theorem PATH_LENGTH_RESTN_0:
     !k v.
       k <= LENGTH v
       ==>
       ((LENGTH(RESTN v k) = XNUM 0) = (LENGTH v = XNUM k))
Proof
   REPEAT GEN_TAC
    THEN Cases_on `v`
    THEN RW_TAC list_ss [LENGTH_RESTN_INFINITE,LENGTH_def,LE]
    THEN RW_TAC list_ss
          [xnum_11,LENGTH_NIL,RESTN_def,LENGTH_def,
           RESTN_FINITE,RESTN_NIL_LENGTH]
QED

Theorem PATH_FINITE_LENGTH_RESTN_0:
     !k v.
       k <= LENGTH v
       ==>
       ((LENGTH(RESTN v k) = XNUM 0) =
        ?l. (LENGTH l = k) /\ (v = FINITE l))
Proof
   REPEAT GEN_TAC
    THEN Cases_on `v`
    THEN RW_TAC list_ss [LENGTH_RESTN_INFINITE,LENGTH_def,LE]
    THEN RW_TAC list_ss
          [xnum_11,LENGTH_NIL,RESTN_def,LENGTH_def,
           RESTN_FINITE,RESTN_NIL_LENGTH]
QED

Theorem LIST_LENGTH_RESTN_0:
     !k l.
       k <= LENGTH l
       ==>
       ((LENGTH(RESTN l k) = 0) = (LENGTH l = k))
Proof
   RW_TAC list_ss [LENGTH_RESTN_INFINITE,LENGTH_def,LE]
    THEN RW_TAC list_ss
          [LENGTH_NIL,RESTN_def,LENGTH_def,
           RESTN_FINITE,RESTN_NIL_LENGTH]
QED

Theorem PATH_FINITE_LENGTH_RESTN_0_COR:
     !k v.
       k < LENGTH v
       ==>
       ((LENGTH(RESTN v k) = XNUM 0) =
        ?l. (LENGTH l = k) /\ (v = FINITE l))
Proof
   PROVE_TAC[LS_LE_X,PATH_FINITE_LENGTH_RESTN_0]
QED

(******************************************************************************
* Unclocked semantics of [!c U (c /\ f)]
******************************************************************************)
Theorem UF_SEM_F_U_CLOCK:
     UF_SEM v (F_U_CLOCK c f) =
      ?j :: LESS(LENGTH v).
        UF_SEM (RESTN v j) (F_AND(F_WEAK_BOOL c,f)) /\
        !i. i < j ==> B_SEM (ELEM v i) (B_NOT c)
Proof
   RW_TAC (arith_ss ++ resq_SS)
    [F_U_CLOCK_def,ELEM_RESTN,UF_SEM_def,CLOCK_TICK_def,LENGTH_SEL]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `k`
       THEN RW_TAC std_ss []
       THEN RES_TAC
       THEN IMP_RES_TAC LS_TRANS_X
       THEN IMP_RES_TAC LS_LE_X
       THEN IMP_RES_TAC PATH_FINITE_LENGTH_RESTN_0
       THEN `~(i=k)` by DECIDE_TAC
       THEN RW_TAC std_ss [],
     Q.EXISTS_TAC `k`
       THEN RW_TAC std_ss []
       THEN RES_TAC
       THEN IMP_RES_TAC LS_TRANS_X
       THEN IMP_RES_TAC LS_LE_X
       THEN IMP_RES_TAC PATH_FINITE_LENGTH_RESTN_0
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC list_ss [LENGTH_def,LS],
     Q.EXISTS_TAC `j`
       THEN RW_TAC std_ss [],
     Q.EXISTS_TAC `j`
       THEN RW_TAC std_ss []]
QED

Theorem COMPLEMENT_LETTER_COMPLEMENT_LETTER:
     COMPLEMENT_LETTER(COMPLEMENT_LETTER l) = l
Proof
   Cases_on `l`
    THEN RW_TAC std_ss [COMPLEMENT_LETTER_def]
QED

Theorem COMPLEMENT_LETTER_COMPLEMENT_LETTER_o:
     COMPLEMENT_LETTER o COMPLEMENT_LETTER = I
Proof
    CONV_TAC FUN_EQ_CONV
     THEN RW_TAC std_ss [COMPLEMENT_LETTER_COMPLEMENT_LETTER]
QED

Theorem MAP_I:
     !l. MAP I l = l
Proof
   Induct
    THEN RW_TAC list_ss []
QED

Theorem COMPLEMENT_COMPLEMENT:
     COMPLEMENT(COMPLEMENT l) = l
Proof
   Cases_on `l`
    THEN RW_TAC std_ss
          [COMPLEMENT_def,MAP_I,MAP_MAP_o,
           COMPLEMENT_LETTER_COMPLEMENT_LETTER_o]
    THEN ONCE_REWRITE_TAC[combinTheory.o_ASSOC]
    THEN REWRITE_TAC
          [COMPLEMENT_LETTER_COMPLEMENT_LETTER_o,combinTheory.I_o_ID]
QED

Theorem LENGTH_COMPLEMENT:
     LENGTH(COMPLEMENT v) = LENGTH v
Proof
   Cases_on `v`
    THEN RW_TAC std_ss
          [COMPLEMENT_def,LENGTH_def,LENGTH_MAP]
QED

Theorem HD_MAP:
     !f l. ~(l=[]) ==> (HD(MAP f l) = f(HD l))
Proof
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss []
QED

Theorem TL_MAP:
     !f l. ~(l=[]) ==> (TL(MAP f l) = MAP f (TL l))
Proof
   GEN_TAC
    THEN Induct
    THEN RW_TAC list_ss []
QED

(* Harder to prove than expected *)
Theorem RESTN_COMPLEMENT:
    !n v. n < LENGTH v ==> (RESTN (COMPLEMENT v) n = COMPLEMENT(RESTN v n))
Proof
   Induct
    THEN Induct
    THEN RW_TAC list_ss [RESTN_def,COMPLEMENT_def,REST_def]
    THEN FULL_SIMP_TAC list_ss [LENGTH_def,LS]
    THENL
     [`0 < LENGTH l` by DECIDE_TAC
       THEN IMP_RES_TAC LENGTH_TL
       THEN `n < LENGTH(TL l)` by DECIDE_TAC
       THEN ASSUM_LIST(fn thl => ASSUME_TAC(Q.SPEC `FINITE(TL l)` (el 5 thl)))
       THEN `~(LENGTH l = 0)` by DECIDE_TAC
       THEN `~(l = [])` by PROVE_TAC[LENGTH_NIL]
       THEN IMP_RES_TAC(Q.ISPEC `COMPLEMENT_LETTER` TL_MAP)
       THEN FULL_SIMP_TAC list_ss [LENGTH_def,LS,COMPLEMENT_def]
       THEN RES_TAC
       THEN RW_TAC list_ss [],
      ASSUM_LIST(fn thl => ASSUME_TAC(Q.SPEC `REST(INFINITE f)` (el 2 thl)))
       THEN FULL_SIMP_TAC list_ss
             [LENGTH_def,LS,COMPLEMENT_def,REST_def,combinTheory.o_DEF]]
QED

val RESTN_COMPLEMENT_COR =
 save_thm
  ("RESTN_COMPLEMENT_COR",
   SIMP_RULE
    std_ss
    [LENGTH_def,LS]
    (ISPECL[``n:num``,``FINITE(l:'a letter list)``]RESTN_COMPLEMENT));

Theorem ELEM_COMPLEMENT:
    !n v. n < LENGTH v ==> (ELEM (COMPLEMENT v) n = COMPLEMENT_LETTER(ELEM v n))
Proof
   Induct
    THEN Induct
    THEN RW_TAC list_ss [RESTN_def,COMPLEMENT_def,REST_def,ELEM_def,HEAD_def]
    THEN FULL_SIMP_TAC list_ss [LENGTH_def,LS]
    THENL
     [Cases_on `l`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss [],
      ASSUM_LIST(fn thl => ASSUME_TAC(Q.SPEC `FINITE(TL l)` (el 2 thl)))
       THEN FULL_SIMP_TAC list_ss [LENGTH_def,LS]
       THEN `0 < LENGTH l` by DECIDE_TAC
       THEN `LENGTH(TL l) = LENGTH l - 1` by PROVE_TAC[LENGTH_TL]
       THEN `n < LENGTH(TL l)` by DECIDE_TAC
       THEN RES_TAC
       THEN FULL_SIMP_TAC list_ss [RESTN_def,COMPLEMENT_def,REST_def,ELEM_def,HEAD_def]
       THEN `~(LENGTH l = 0)` by DECIDE_TAC
       THEN `~(l = [])` by PROVE_TAC[LENGTH_NIL]
       THEN IMP_RES_TAC(Q.ISPEC `COMPLEMENT_LETTER` TL_MAP)
       THEN RW_TAC std_ss [],
      ASSUM_LIST(fn thl => ASSUME_TAC(Q.SPEC `REST(INFINITE f)` (el 2 thl)))
       THEN FULL_SIMP_TAC list_ss
             [LENGTH_def,LS,COMPLEMENT_def,REST_def,combinTheory.o_DEF,
              RESTN_def,COMPLEMENT_def,REST_def,ELEM_def,HEAD_def]]
QED

val ELEM_COMPLEMENT_COR =
 save_thm
  ("ELEM_COMPLEMENT_COR",
   SIMP_RULE
    std_ss
    [LENGTH_def,LS]
    (ISPECL[``n:num``,``FINITE(l:'a letter list)``]ELEM_COMPLEMENT));

(******************************************************************************
* Formula disjunction: f1 \/ f2
******************************************************************************)
Theorem UF_SEM_F_OR:
     UF_SEM v (F_OR(f1,f2)) = UF_SEM v f1 \/ UF_SEM v f2
Proof
   RW_TAC (std_ss ++ resq_SS) [UF_SEM_def,F_OR_def,COMPLEMENT_COMPLEMENT]
QED

(******************************************************************************
* Formula conjunction: f1 /\ f2
******************************************************************************)
Theorem UF_SEM_F_AND:
     UF_SEM v (F_AND(f1,f2)) = UF_SEM v f1 /\ UF_SEM v f2
Proof
   RW_TAC (std_ss ++ resq_SS) [UF_SEM_def]
QED

(******************************************************************************
* Formula implication: f1 --> f2
******************************************************************************)
Theorem UF_SEM_F_IMPLIES:
     UF_SEM v (F_IMPLIES (f1,f2)) = UF_SEM (COMPLEMENT v) f1 ==> UF_SEM v f2
Proof
   RW_TAC (std_ss ++ resq_SS) [UF_SEM_def,F_IMPLIES_def,UF_SEM_F_OR]
    THEN PROVE_TAC[]
QED

Theorem UF_SEM_RESTN_F_WEAK_BOOL:
     !j v.
      j < LENGTH v
      ==>
      (UF_SEM (RESTN v j) (F_WEAK_BOOL b) = B_SEM (ELEM v j) b)
Proof
   RW_TAC list_ss [UF_SEM_def,ELEM_RESTN]
    THEN EQ_TAC
    THEN RW_TAC list_ss []
    THEN IMP_RES_TAC LS_LE_X
    THEN IMP_RES_TAC PATH_LENGTH_RESTN_0
    THEN `j < XNUM j` by PROVE_TAC[]
    THEN FULL_SIMP_TAC list_ss [LS]
QED

Theorem UF_SEM_RESTN_F_WEAK_BOOL_COR:
     !j v.
      j < LENGTH v /\ UF_SEM (RESTN v j) (F_WEAK_BOOL b) =
      j < LENGTH v /\ B_SEM (ELEM v j) b
Proof
   PROVE_TAC[UF_SEM_RESTN_F_WEAK_BOOL]
QED

(******************************************************************************
* Eventually: F f (implication)
******************************************************************************)
Theorem UF_SEM_F_F_IMP:
     UF_SEM v (F_F f) ==> ?i :: LESS(LENGTH v). UF_SEM (RESTN v i) f
Proof
   RW_TAC (arith_ss ++ resq_SS) [UF_SEM_def,F_F_def,B_SEM_def]
    THEN Cases_on `v`
    THEN RW_TAC arith_ss
          [xnum_to_def,LENGTH_def,GT_xnum_num_def,RESTN_FINITE,LENGTH_def,
           FinitePSLPathTheory.LENGTH_RESTN,LENGTH_RESTN_INFINITE,LS]
    THEN Q.EXISTS_TAC `k`
    THEN RW_TAC arith_ss [FinitePSLPathTheory.LENGTH_RESTN,GSYM RESTN_FINITE]
    THEN PROVE_TAC[LENGTH_def,LS]
QED

(******************************************************************************
* Eventually: F f (equation)
* N.B. Probably can simplify proof to avoid cases on v, as in UF_SEM_F_G
******************************************************************************)
Theorem UF_SEM_F_F:
     UF_SEM v (F_F f) =
      ?i :: LESS(LENGTH v).
        UF_SEM (RESTN v i) f
        /\
        !j :: LESS i. (ELEM v j = BOTTOM) ==> (LENGTH v = XNUM j)
Proof
   RW_TAC (arith_ss ++ resq_SS) [UF_SEM_def,F_F_def,B_SEM_def]
    THEN Cases_on `v`
    THEN RW_TAC arith_ss
          [xnum_to_def,LENGTH_def,GT_xnum_num_def,RESTN_FINITE,LENGTH_def,
           FinitePSLPathTheory.LENGTH_RESTN,LENGTH_RESTN_INFINITE]
    THEN EQ_TAC
    THEN RW_TAC arith_ss []
    THENL
     [Q.EXISTS_TAC `k`
       THEN RW_TAC arith_ss []
       THEN RES_TAC
       THEN FULL_SIMP_TAC list_ss [LS,GSYM RESTN_FINITE,ELEM_RESTN]
       THEN `j <= LENGTH l` by DECIDE_TAC
       THEN IMP_RES_TAC LIST_LENGTH_RESTN_0
       THEN TRY DECIDE_TAC >- fs []
       THEN PROVE_TAC[B_SEM_def],
      Q.EXISTS_TAC `i`
       THEN RW_TAC arith_ss []
       THEN RES_TAC
       THEN FULL_SIMP_TAC list_ss [LS,GSYM RESTN_FINITE,ELEM_RESTN]
       THEN `j <= LENGTH l` by DECIDE_TAC
       THEN IMP_RES_TAC LIST_LENGTH_RESTN_0
       THEN RW_TAC std_ss []
       THEN Cases_on `LENGTH l = j` (* 2 subgoals *)
       THEN RW_TAC std_ss [] >- fs []
       THEN `~(ELEM (FINITE l) j = BOTTOM)` by PROVE_TAC[]
       THEN Cases_on `ELEM (FINITE l) j`
       THEN RW_TAC std_ss [B_SEM_def],
      Q.EXISTS_TAC `k`
       THEN RW_TAC arith_ss []
       THEN RES_TAC
       THEN FULL_SIMP_TAC list_ss [ELEM_RESTN]
       THEN Cases_on `ELEM (INFINITE f') j`
       THEN RW_TAC std_ss [B_SEM_def]
       THEN FULL_SIMP_TAC list_ss [B_SEM_def],
      Q.EXISTS_TAC `i`
       THEN RW_TAC arith_ss []
       THEN RES_TAC
       THEN FULL_SIMP_TAC list_ss [ELEM_RESTN]
       THEN Cases_on `ELEM (INFINITE f') j`
       THEN RW_TAC std_ss [B_SEM_def]]
QED

(******************************************************************************
* Globally: G f
******************************************************************************)
val UF_SEM_F_G_LEMMA =
 SIMP_CONV  (arith_ss ++ resq_SS)
    [F_G_def,UF_SEM_def,UF_SEM_F_F,LENGTH_COMPLEMENT,
     DECIDE ``~A \/ B \/ C = A ==> (B \/ C)``]
    ``UF_SEM v (F_G f)``;

Theorem UF_SEM_F_G:
     UF_SEM v (F_G f) =
      !i :: LESS(LENGTH v).
        UF_SEM (RESTN v i) f
        \/
        ?j :: LESS i. (ELEM v j = TOP) /\ ~(LENGTH v = XNUM j)
Proof
   RW_TAC (arith_ss ++ resq_SS) [UF_SEM_F_G_LEMMA]
    THEN EQ_TAC
    THEN RW_TAC arith_ss []
    THEN RES_TAC
    THENL
     [IMP_RES_TAC RESTN_COMPLEMENT
       THEN PROVE_TAC[COMPLEMENT_COMPLEMENT],
      DISJ2_TAC
       THEN Q.EXISTS_TAC `j`
       THEN RW_TAC arith_ss []
       THEN `j < LENGTH v` by PROVE_TAC[LS_TRANS_X]
       THEN IMP_RES_TAC ELEM_COMPLEMENT
       THEN `COMPLEMENT_LETTER (ELEM v j) = BOTTOM` by PROVE_TAC[]
       THEN POP_ASSUM(fn th => ASSUME_TAC(AP_TERM ``COMPLEMENT_LETTER`` th))
       THEN FULL_SIMP_TAC std_ss
             [COMPLEMENT_LETTER_COMPLEMENT_LETTER,COMPLEMENT_LETTER_def],
      IMP_RES_TAC RESTN_COMPLEMENT
       THEN PROVE_TAC[COMPLEMENT_COMPLEMENT],
      DISJ2_TAC
       THEN Q.EXISTS_TAC `j`
       THEN RW_TAC arith_ss []
       THEN `j < LENGTH v` by PROVE_TAC[LS_TRANS_X]
       THEN IMP_RES_TAC ELEM_COMPLEMENT
       THEN RW_TAC std_ss [COMPLEMENT_LETTER_def]]
QED

(******************************************************************************
* Unclocked semantics of [!c W (c /\ f)]
******************************************************************************)
val UF_SEM_F_W_CLOCK_LEMMA =
 SIMP_CONV  (arith_ss ++ resq_SS)
    [UF_SEM_F_G,UF_SEM_def,F_W_CLOCK_def,F_W_def,GSYM F_U_CLOCK_def,
     UF_SEM_F_OR,ELEM_RESTN]
    ``UF_SEM v (F_W_CLOCK c f)``;

Theorem UF_SEM_F_W_CLOCK:
     UF_SEM v (F_W_CLOCK c f) =
      UF_SEM v (F_U_CLOCK c f)
      \/
      !i :: LESS(LENGTH v).
        B_SEM (ELEM v i) (B_NOT c) \/ ?j :: LESS i. ELEM v j = TOP
Proof
   RW_TAC (arith_ss ++ resq_SS)
    [F_W_CLOCK_def,UF_SEM_def,UF_SEM_F_W_CLOCK_LEMMA]
    THEN EQ_TAC
    THEN ZAP_TAC std_ss []
    THEN RW_TAC std_ss []
    THEN DISJ2_TAC
    THEN RW_TAC std_ss []
    THEN RES_TAC
    THEN ZAP_TAC std_ss []
    THENL
     [IMP_RES_TAC LS_LE_X
       THEN IMP_RES_TAC PATH_LENGTH_RESTN_0
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC list_ss [LS],
      DISJ2_TAC
       THEN Q.EXISTS_TAC `j`
       THEN RW_TAC std_ss []
       THEN Cases_on `LENGTH v = XNUM j`
       THEN RW_TAC std_ss []
       THEN IMP_RES_TAC LS_TRANS_X
       THEN `j < XNUM j` by PROVE_TAC[]
       THEN FULL_SIMP_TAC list_ss [LS]]
QED

local

val AUX_TAC1 =
 Q.EXISTS_TAC `j`
  THEN RW_TAC arith_ss [ELEM_RESTN]
  THEN IMP_RES_TAC LS_LE_X
  THEN IMP_RES_TAC PATH_FINITE_LENGTH_RESTN_0
  THEN FULL_SIMP_TAC list_ss [LENGTH_def,LS]

in

Theorem F_STRONG_BOOL_CLOCK_COMP:
     !b v c. F_SEM v c (F_STRONG_BOOL b) =
              UF_SEM v (F_CLOCK_COMP c (F_STRONG_BOOL b))
Proof
   RW_TAC (arith_ss  ++ resq_SS)
    [F_SEM_def,UF_SEM_def,F_CLOCK_COMP_def,UF_SEM_F_U_CLOCK,
     CLOCK_TICK_def,LENGTH_SEL,ELEM_EL]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `j`
       THEN RW_TAC arith_ss [ELEM_RESTN]
       THENL
        [`0 <= j /\ j <= j` by DECIDE_TAC
          THEN IMP_RES_TAC
                (INST_TYPE[{redex=``:'a``, residue=``:'a letter``}]EL_SEL)
          THEN FULL_SIMP_TAC arith_ss [],
         RES_TAC
          THEN `0 <= i /\ i <= j` by DECIDE_TAC
          THEN IMP_RES_TAC
                (INST_TYPE[{redex=``:'a``, residue=``:'a letter``}]EL_SEL)
          THEN FULL_SIMP_TAC arith_ss []],
     AUX_TAC1,
     AUX_TAC1,
     AUX_TAC1,
     Q.EXISTS_TAC `j`
       THEN FULL_SIMP_TAC arith_ss [ELEM_RESTN]
       THEN `0 <= j /\ j <= j` by DECIDE_TAC
       THEN IMP_RES_TAC
             (INST_TYPE[{redex=``:'a``, residue=``:'a letter``}]EL_SEL)
       THEN FULL_SIMP_TAC arith_ss [ELEM_EL]
       THEN RW_TAC std_ss []
       THEN `0 <= i /\ i <= j` by DECIDE_TAC
       THEN IMP_RES_TAC
             (INST_TYPE[{redex=``:'a``, residue=``:'a letter``}]EL_SEL)
       THEN FULL_SIMP_TAC arith_ss [ELEM_EL]]
QED

end;

(*
val th =
 SIMP_CONV
  (list_ss ++ resq_SS)
    [F_SEM_def,UF_SEM_def,F_CLOCK_COMP_def,UF_SEM_F_U_CLOCK,CLOCK_TICK_def,
     F_W_CLOCK_def,ELEM_RESTN,UF_SEM_def,CLOCK_TICK_def,LENGTH_SEL,
     F_W_def,F_F_def,F_G_def,UF_SEM_F_OR,UF_SEM_F_U_CLOCK,LENGTH_COMPLEMENT,
     ELEM_EL,RESTN_def,RESTN_FINITE,ELEM_def,COMPLEMENT_def,LS,
     DECIDE ``m < 1 = (m=0)``, DECIDE ``m < 2 = (m=0) \/ (m=1)``,
     COMPLEMENT_LETTER_def,FinitePSLPathTheory.RESTN_def,
     HEAD_def,B_SEM_def,xnum_11,HD_SEL]
  ``F_SEM (FINITE[BOTTOM]) c (F_WEAK_BOOL b) =
     UF_SEM (FINITE[BOTTOM]) (F_CLOCK_COMP c (F_WEAK_BOOL b))``;
*)

val WOP_EQ =
 prove
  (``!P. (?n:num. P n) = ?n. P n /\ !m. m < n ==> ~P m``,
   PROVE_TAC[WOP]);

val WOP_IMP =
 prove
  (``!P n. P(n:num) ==> ?n. P n /\ !m. m < n ==> ~P m``,
   PROVE_TAC[WOP]);


(*
Lemma below is one of the most messy proofs I've ever done!  There is
a frequented repeated well-foundedness argument, that occurrs several
times inlined, which needs to be extracted into a lemma.
*)

val EL_SEL_LEMMA1 =
 SIMP_RULE arith_ss [] (SPECL[``0``,``j:num``, ``j:num``]EL_SEL);

val EL_SEL_LEMMA2 =
 SIMP_RULE arith_ss [] (SPECL[``0``,``i:num``, ``j:num``]EL_SEL);

Theorem F_WEAK_BOOL_CLOCK_COMP_IMP1:
     !b v c. F_SEM v c (F_WEAK_BOOL b) ==>
              UF_SEM v (F_CLOCK_COMP c (F_WEAK_BOOL b))
Proof
   SIMP_TAC (arith_ss  ++ resq_SS) [F_SEM_def]
    THEN SIMP_TAC (list_ss ++ resq_SS)
          [CLOCK_TICK_def,LENGTH_SEL,ELEM_EL,
           EL_SEL_LEMMA1,EL_SEL_LEMMA2]
    THEN SIMP_TAC (list_ss ++ resq_SS)
          [F_CLOCK_COMP_def,UF_SEM_F_W_CLOCK,UF_SEM_F_U_CLOCK,UF_SEM_F_AND]
    THEN ONCE_REWRITE_TAC
          [DECIDE ``A /\ (B /\ C) /\ D = A /\ ((A /\ B) /\ (A /\ C)) /\ D``]
    THEN SIMP_TAC (list_ss ++ resq_SS)
          [UF_SEM_RESTN_F_WEAK_BOOL_COR]
    THEN ONCE_REWRITE_TAC
          [DECIDE ``A /\ ((A /\ B) /\ (A /\ C)) /\ D = A /\ B /\ C /\ D``]
    THEN RW_TAC std_ss []
    THEN Cases_on
          `?j. j < LENGTH v /\
               B_SEM (ELEM (COMPLEMENT v) j) c /\
               (!i. i < j ==> B_SEM (ELEM (COMPLEMENT v) i) (B_NOT c))`
    THENL
     [POP_ASSUM STRIP_ASSUME_TAC
       THEN RES_TAC
       THEN Cases_on
             `!i. i < LENGTH v ==>
                  B_SEM (ELEM v i) (B_NOT c) \/ ?j. j < i /\ (ELEM v j = TOP)`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM,DECIDE``~A \/ B = A ==> B``]
       THEN Q.EXISTS_TAC `j`
       THEN RW_TAC std_ss []
       THENL
        [Cases_on `ELEM v j`
          THEN FULL_SIMP_TAC std_ss [B_SEM_def,COMPLEMENT_LETTER_def]
          THEN IMP_RES_TAC ELEM_COMPLEMENT
          THEN PROVE_TAC[COMPLEMENT_LETTER_def],
         `i' < LENGTH v` by PROVE_TAC[LS_TRANS_X]
          THEN RES_TAC
          THEN Cases_on `ELEM v i'`
          THEN FULL_SIMP_TAC std_ss [B_SEM_def,COMPLEMENT_LETTER_def]
          THEN IMP_RES_TAC ELEM_COMPLEMENT
          THENL
           [`ELEM (COMPLEMENT v) i' = TOP`
              by PROVE_TAC[COMPLEMENT_LETTER_def]
             THEN ASSUM_LIST(fn thl => FULL_SIMP_TAC std_ss [el 1 thl])
             THEN `B_SEM (COMPLEMENT_LETTER BOTTOM) c` by
                   SIMP_TAC std_ss [B_SEM_def,COMPLEMENT_LETTER_def]
             THEN `?i''. i'' < i' /\ ~B_SEM (ELEM (COMPLEMENT v) i'') (B_NOT c)`
                   by PROVE_TAC[]
             THEN `i'' < j` by DECIDE_TAC
             THEN PROVE_TAC[],
            `B_SEM (STATE f) (B_NOT c)` by PROVE_TAC[COMPLEMENT_LETTER_def]
              THEN FULL_SIMP_TAC std_ss [B_SEM_def]]],
      FULL_SIMP_TAC std_ss [NOT_EXISTS_THM]
       THEN FULL_SIMP_TAC std_ss
             [DECIDE ``~A \/ ~B \/ C = A ==> B ==> C``]
       THEN DISJ2_TAC
       THEN RW_TAC std_ss []
       THEN Cases_on `?j. j < i /\ (ELEM v j = TOP)`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_EXISTS_THM,DECIDE ``~A \/ B = A ==> B``]
       THEN Cases_on `B_SEM (ELEM v i) (B_NOT c)`
       THEN RW_TAC std_ss []
       THEN Cases_on `ELEM v i`
       THEN RW_TAC std_ss []
       THENL
        [POP_ASSUM(fn th => FULL_SIMP_TAC std_ss [th,B_SEM_def]),
         ASSUM_LIST
          (fn thl =>
            STRIP_ASSUME_TAC
             (SIMP_RULE std_ss
               [el 1 thl,el 4 thl,ELEM_COMPLEMENT,COMPLEMENT_LETTER_def,B_SEM_def]
               (Q.SPEC `i` (el 5 thl))))
          THEN `i' < LENGTH v` by PROVE_TAC [LS_TRANS_X]
          THEN Cases_on `ELEM v i'`
          THEN RW_TAC std_ss []
          THENL
           [RES_TAC,
            IMP_RES_TAC ELEM_COMPLEMENT
             THEN ASSUM_LIST
                   (fn thl =>
                     STRIP_ASSUME_TAC
                      (SIMP_RULE std_ss
                        [el 2 thl,el 3 thl,ELEM_COMPLEMENT,
                         COMPLEMENT_LETTER_def,B_SEM_def]
                        (el 5 thl))),
            POP_ASSUM
             (fn th =>
               ASSUME_TAC
                (EXISTS(mk_exists(``f:'a -> bool``,concl th),``f:'a -> bool``)th))
            THEN ASSUM_LIST
                  (fn thl =>
                    ASSUME_TAC
                     (LIST_CONJ[el 1 thl,el 3 thl,el 4 thl]))
            THEN POP_ASSUM
                   (fn th =>
                     STRIP_ASSUME_TAC
                      (MP
                        (BETA_RULE
                          (ISPECL[mk_abs(``i':num``,concl th),``i':num``]WOP_IMP))
                        th))
            THEN `n < LENGTH v` by PROVE_TAC [LS_TRANS_X]
            THEN `ELEM (COMPLEMENT v) n = STATE f`
                  by PROVE_TAC[ELEM_COMPLEMENT,COMPLEMENT_LETTER_def]
            THEN ASSUM_LIST
                  (fn thl =>
                    ASSUME_TAC(SIMP_RULE std_ss [el 1 thl,B_SEM_def](el 5 thl)))
            THEN `B_SEM (ELEM (COMPLEMENT v) n) c` by PROVE_TAC[]
            THEN ASSUM_LIST
                  (fn thl =>
                    STRIP_ASSUME_TAC
                      (SIMP_RULE std_ss [el 1 thl,el 4 thl](Q.SPEC `n` (el 17 thl))))
            THEN `i'' < i` by DECIDE_TAC
            THEN Cases_on `ELEM v i''`
            THEN RW_TAC std_ss []
            THENL
             [RES_TAC,
              `i'' < LENGTH v` by PROVE_TAC [LS_TRANS_X]
               THEN IMP_RES_TAC ELEM_COMPLEMENT
               THEN ASSUM_LIST
                     (fn thl =>
                       STRIP_ASSUME_TAC
                        (SIMP_RULE std_ss
                          [el 4 thl,el 7 thl,ELEM_COMPLEMENT,
                           COMPLEMENT_LETTER_def,B_SEM_def]
                          (el 9 thl))),
              RES_TAC]],
           `B_SEM (ELEM v i) c` by PROVE_TAC[B_SEM_def]
            THEN `B_SEM (ELEM (COMPLEMENT v) i) c`
                   by PROVE_TAC[ELEM_COMPLEMENT,COMPLEMENT_LETTER_def]
            THEN ASSUM_LIST
                  (fn thl =>
                    STRIP_ASSUME_TAC(SIMP_RULE std_ss
                     [el 1 thl,el 6 thl](Q.SPEC `i` (el 7 thl))))
            THEN Cases_on `ELEM v i'`
            THEN RW_TAC std_ss []
            THENL
             [RES_TAC,
              `i' < LENGTH v` by PROVE_TAC [LS_TRANS_X]
               THEN IMP_RES_TAC ELEM_COMPLEMENT
               THEN ASSUM_LIST
                     (fn thl =>
                       STRIP_ASSUME_TAC
                        (SIMP_RULE std_ss
                          [el 2 thl,el 4 thl,
                           COMPLEMENT_LETTER_def,B_SEM_def]
                          (el 5 thl))),
              `i' < LENGTH v` by PROVE_TAC[LS_TRANS_X]
               THEN `ELEM (COMPLEMENT v) i' = STATE f'`
                     by PROVE_TAC[ELEM_COMPLEMENT,COMPLEMENT_LETTER_def]
            THEN ASSUM_LIST
                  (fn thl =>
                    ASSUME_TAC
                     (EXISTS
                      (mk_exists
                       (``f':'a -> bool``,concl(el 1 thl)),``f':'a -> bool``)(el 1 thl)))
            THEN ASSUM_LIST
                  (fn thl =>
                    ASSUME_TAC
                     (LIST_CONJ[el 1 thl,el 5 thl,el 6 thl]))
            THEN POP_ASSUM
                   (fn th =>
                     STRIP_ASSUME_TAC
                      (MP
                        (BETA_RULE
                          (ISPECL[mk_abs(``i':num``,concl th),``i':num``]WOP_IMP))
                        th))
            THEN `n < LENGTH v` by PROVE_TAC[LS_TRANS_X]
            THEN Cases_on `ELEM v n`
            THEN RW_TAC std_ss []
            THENL
             [RES_TAC,
              IMP_RES_TAC ELEM_COMPLEMENT
               THEN ASSUM_LIST
                     (fn thl =>
                       STRIP_ASSUME_TAC
                        (SIMP_RULE std_ss
                          [el 3 thl,el 5 thl,
                           COMPLEMENT_LETTER_def,B_SEM_def]
                          (el 9 thl))),
              IMP_RES_TAC ELEM_COMPLEMENT
               THEN ASSUM_LIST
                     (fn thl =>
                       STRIP_ASSUME_TAC
                        (SIMP_RULE std_ss
                          [el 3 thl,el 5 thl,
                           COMPLEMENT_LETTER_def,B_SEM_def]
                          (el 9 thl)))
               THEN `B_SEM (ELEM (COMPLEMENT v) n) c` by PROVE_TAC[COMPLEMENT_LETTER_def]
               THEN ASSUM_LIST
                     (fn thl =>
                       STRIP_ASSUME_TAC(SIMP_RULE std_ss
                        [el 1 thl,el 8 thl](Q.SPEC `n` (el 24 thl))))
               THEN `i'' < i` by DECIDE_TAC
               THEN ASSUM_LIST
                     (fn thl =>
                       STRIP_ASSUME_TAC(SIMP_RULE std_ss
                        [el 2 thl,el 3 thl,el 11 thl](Q.SPEC `i''` (el 12 thl))))
            THEN Cases_on `ELEM v i''`
            THEN RW_TAC std_ss []
            THENL
             [RES_TAC,
              `i'' < LENGTH v` by PROVE_TAC [LS_TRANS_X]
               THEN IMP_RES_TAC ELEM_COMPLEMENT
               THEN ASSUM_LIST
                     (fn thl =>
                       STRIP_ASSUME_TAC
                        (SIMP_RULE std_ss
                          [el 1 thl,el 3 thl,
                           COMPLEMENT_LETTER_def,B_SEM_def]
                          (el 6 thl))),
              `i'' < LENGTH v` by PROVE_TAC [LS_TRANS_X]
               THEN IMP_RES_TAC ELEM_COMPLEMENT
               THEN `ELEM (COMPLEMENT v) i'' = STATE f'''''`
                    by PROVE_TAC[COMPLEMENT_LETTER_def]
               THEN RES_TAC]]]]]
QED

Theorem F_WEAK_BOOL_CLOCK_COMP_IMP2:
     !b v c. UF_SEM v (F_CLOCK_COMP c (F_WEAK_BOOL b)) ==>
              F_SEM v c (F_WEAK_BOOL b)
Proof
   SIMP_TAC (arith_ss  ++ resq_SS) [F_SEM_def]
    THEN SIMP_TAC (list_ss ++ resq_SS)
          [CLOCK_TICK_def,LENGTH_SEL,ELEM_EL,
           EL_SEL_LEMMA1,EL_SEL_LEMMA2]
    THEN SIMP_TAC (list_ss ++ resq_SS)
          [F_CLOCK_COMP_def,UF_SEM_F_W_CLOCK,UF_SEM_F_U_CLOCK,UF_SEM_F_AND]
    THEN ONCE_REWRITE_TAC
          [DECIDE ``A /\ (B /\ C) /\ D = A /\ ((A /\ B) /\ (A /\ C)) /\ D``]
    THEN SIMP_TAC (list_ss ++ resq_SS)
          [UF_SEM_RESTN_F_WEAK_BOOL_COR]
    THEN ONCE_REWRITE_TAC
          [DECIDE ``A /\ ((A /\ B) /\ (A /\ C)) /\ D = A /\ B /\ C /\ D``]
    THEN RW_TAC std_ss []
    THENL
     [Cases_on `j:num = j'`
       THEN RW_TAC std_ss []
       THEN `j < j' \/ j' < j` by DECIDE_TAC
       THEN RES_TAC
       THENL
        [Cases_on `ELEM v j`
          THEN RW_TAC std_ss []
          THENL
           [IMP_RES_TAC ELEM_COMPLEMENT
             THEN `ELEM (COMPLEMENT v) j = BOTTOM` by PROVE_TAC[COMPLEMENT_LETTER_def]
             THEN PROVE_TAC[B_SEM_def],
            IMP_RES_TAC ELEM_COMPLEMENT
             THEN `ELEM (COMPLEMENT v) j = TOP` by PROVE_TAC[COMPLEMENT_LETTER_def]
             THEN PROVE_TAC[B_SEM_def],
            IMP_RES_TAC ELEM_COMPLEMENT
             THEN `ELEM (COMPLEMENT v) j = STATE f` by PROVE_TAC[COMPLEMENT_LETTER_def]
             THEN PROVE_TAC[B_SEM_def]],
         Cases_on `ELEM v j'`
          THEN RW_TAC std_ss []
          THENL
           [IMP_RES_TAC ELEM_COMPLEMENT
             THEN `ELEM (COMPLEMENT v) j' = BOTTOM` by PROVE_TAC[COMPLEMENT_LETTER_def]
             THEN PROVE_TAC[B_SEM_def],
            IMP_RES_TAC ELEM_COMPLEMENT
             THEN `ELEM (COMPLEMENT v) j' = TOP` by PROVE_TAC[COMPLEMENT_LETTER_def]
             THEN PROVE_TAC[B_SEM_def],
            IMP_RES_TAC ELEM_COMPLEMENT
             THEN `ELEM (COMPLEMENT v) j' = STATE f` by PROVE_TAC[COMPLEMENT_LETTER_def]
             THEN PROVE_TAC[B_SEM_def]]],
      RES_TAC
       THENL
        [Cases_on `ELEM v j`
          THEN RW_TAC std_ss []
          THENL
           [IMP_RES_TAC ELEM_COMPLEMENT
             THEN `ELEM (COMPLEMENT v) j = BOTTOM` by PROVE_TAC[COMPLEMENT_LETTER_def]
             THEN PROVE_TAC[B_SEM_def],
            IMP_RES_TAC ELEM_COMPLEMENT
             THEN `ELEM (COMPLEMENT v) j = TOP` by PROVE_TAC[COMPLEMENT_LETTER_def]
             THEN PROVE_TAC[B_SEM_def],
            IMP_RES_TAC ELEM_COMPLEMENT
             THEN `ELEM (COMPLEMENT v) j = STATE f` by PROVE_TAC[COMPLEMENT_LETTER_def]
             THEN PROVE_TAC[B_SEM_def]],
         `B_SEM (ELEM (COMPLEMENT v) j') (B_NOT c)` by PROVE_TAC[]
          THEN `j' < LENGTH v` by PROVE_TAC[LS_TRANS_X]
          THEN IMP_RES_TAC ELEM_COMPLEMENT
          THEN `ELEM (COMPLEMENT v) j' = BOTTOM` by PROVE_TAC[COMPLEMENT_LETTER_def]
          THEN PROVE_TAC[B_SEM_def]]]
QED

Theorem F_WEAK_BOOL_CLOCK_COMP:
     !b v c. F_SEM v c (F_WEAK_BOOL b) =
              UF_SEM v (F_CLOCK_COMP c (F_WEAK_BOOL b))
Proof
   PROVE_TAC
    [F_WEAK_BOOL_CLOCK_COMP_IMP1,F_WEAK_BOOL_CLOCK_COMP_IMP2]
QED

Theorem EL_SEL_THM:
     !p. i + n <= j ==> (EL n (SEL p (i,j)) = ELEM p (i + n))
Proof
   PROVE_TAC[SIMP_RULE arith_ss [] (Q.SPECL[`i`,`n+i`,`j`]EL_SEL)]
QED

Theorem F_NEXT_CLOCK_COMP_IMP1:
     !f.
       (!v c.
         F_SEM v c f = UF_SEM v (F_CLOCK_COMP c f))
       ==>
       !v c.
         F_SEM v c (F_NEXT f) ==> UF_SEM v (F_CLOCK_COMP c (F_NEXT f))
Proof
    SIMP_TAC (arith_ss++resq_SS)
       [F_SEM_def,UF_SEM_def,F_CLOCK_COMP_def,CLOCK_TICK_def]
       THEN SIMP_TAC (arith_ss++resq_SS)
             [UF_SEM_F_U_CLOCK,RESTN_RESTN,LENGTH_SEL,UF_SEM_F_AND,
              EL_SEL_LEMMA1,EL_SEL_LEMMA2,ELEM_EL]
       THEN ONCE_REWRITE_TAC
             [DECIDE ``A /\ (B /\ C) /\ D = A /\ ((A /\ B) /\ (A /\ C)) /\ D``]
       THEN SIMP_TAC (list_ss ++ resq_SS)
             [UF_SEM_RESTN_F_WEAK_BOOL_COR]
       THEN ONCE_REWRITE_TAC
             [DECIDE ``A /\ ((A /\ B) /\ (A /\ C)) /\ D = A /\ B /\ C /\ D``]
       THEN SIMP_TAC (arith_ss++resq_SS)
             [UF_SEM_def,RESTN_RESTN,UF_SEM_F_U_CLOCK]
       THEN RW_TAC std_ss []
       THEN Q.EXISTS_TAC `j`
       THEN RW_TAC list_ss []
       THENL
        [Cases_on `v`
          THEN RW_TAC list_ss
                [GT,LENGTH_RESTN_INFINITE,
                 IS_FINITE_def,LENGTH_RESTN,LENGTH_def,SUB]
          THEN FULL_SIMP_TAC list_ss [LENGTH_def,LS],
         RW_TAC list_ss [ELEM_RESTN]
          THEN `(j + 1) + (k - (j + 1)) <= k` by DECIDE_TAC
          THEN IMP_RES_TAC(ISPEC ``v :'a letter path`` EL_SEL_THM)
          THEN `j + 1 + (k - (j + 1)) = k` by DECIDE_TAC
          THEN `B_SEM (ELEM v k) c` by PROVE_TAC[]
          THEN `j + 1 <= k` by DECIDE_TAC
          THEN Q.EXISTS_TAC `k - (j + 1)`
          THEN RW_TAC list_ss []
          THENL
           [Cases_on `v`
             THEN RW_TAC list_ss
                   [GT,LENGTH_RESTN_INFINITE,RESTN_FINITE,
                    IS_FINITE_def,LENGTH_RESTN,LENGTH_def,SUB]
             THEN FULL_SIMP_TAC list_ss [LENGTH_def,LS]
             THEN RW_TAC list_ss [FinitePSLPathTheory.LENGTH_RESTN],
            `(j + 1) + i <= k` by DECIDE_TAC
             THEN RES_TAC
             THEN `i + (j + 1) = (j + 1) + i` by DECIDE_TAC
             THEN PROVE_TAC[EL_SEL_THM]]]
QED

Theorem F_NEXT_CLOCK_COMP_IMP2:
     !f. (!v c. F_SEM v c f = UF_SEM v (F_CLOCK_COMP c f))
         ==>
         !v c. UF_SEM v (F_CLOCK_COMP c (F_NEXT f)) ==> F_SEM v c (F_NEXT f)
Proof
      SIMP_TAC (arith_ss++resq_SS)
       [F_SEM_def,UF_SEM_def,F_CLOCK_COMP_def,CLOCK_TICK_def]
       THEN SIMP_TAC (arith_ss++resq_SS)
             [UF_SEM_F_U_CLOCK,RESTN_RESTN,LENGTH_SEL,UF_SEM_F_AND,
              EL_SEL_LEMMA1,EL_SEL_LEMMA2,ELEM_EL]
       THEN ONCE_REWRITE_TAC
             [DECIDE ``A /\ (B /\ C) /\ D = A /\ ((A /\ B) /\ (A /\ C)) /\ D``]
       THEN SIMP_TAC (list_ss ++ resq_SS)
             [UF_SEM_RESTN_F_WEAK_BOOL_COR]
       THEN ONCE_REWRITE_TAC
             [DECIDE ``A /\ ((A /\ B) /\ (A /\ C)) /\ D = A /\ B /\ C /\ D``]
       THEN SIMP_TAC (arith_ss++resq_SS)
             [UF_SEM_def,RESTN_RESTN,UF_SEM_F_U_CLOCK]
       THEN RW_TAC std_ss []
       THENL
        [Q.EXISTS_TAC `j`
          THEN RW_TAC list_ss []
          THEN Q.EXISTS_TAC `j + (j' + 1)`
          THEN STRONG_CONJ_TAC THEN RW_TAC list_ss []
          THENL
           [Cases_on `v`
             THEN RW_TAC list_ss
                   [GT,LENGTH_RESTN_INFINITE,RESTN_FINITE,
                    IS_FINITE_def,LENGTH_RESTN,LENGTH_def,SUB]
             THEN FULL_SIMP_TAC list_ss [LENGTH_def,LS,RESTN_FINITE,xnum_11,GT]
             THEN `LENGTH(RESTN l j) = LENGTH l - j`
                   by PROVE_TAC[FinitePSLPathTheory.LENGTH_RESTN]
             THEN `j + 1 < LENGTH l` by DECIDE_TAC
             THEN `LENGTH(RESTN l (j + 1)) = LENGTH l - (j + 1)`
                   by PROVE_TAC[FinitePSLPathTheory.LENGTH_RESTN]
             THEN DECIDE_TAC,
            RW_TAC list_ss [EL_SEL_THM]
            THEN `?l. (LENGTH l = j + (j' + 1)) /\ (v = FINITE l)`
                by PROVE_TAC[PATH_FINITE_LENGTH_RESTN_0_COR]
            THEN RW_TAC std_ss []
            THEN FULL_SIMP_TAC list_ss [LENGTH_def,LS],
            RW_TAC list_ss [EL_SEL_THM]
            THEN `?l. (LENGTH l = j + (j' + 1)) /\ (v = FINITE l)`
                by PROVE_TAC[PATH_FINITE_LENGTH_RESTN_0_COR]
            THEN RW_TAC std_ss []
            THEN FULL_SIMP_TAC list_ss [LENGTH_def,LS]],
         Q.EXISTS_TAC `j`
          THEN RW_TAC list_ss []
          THEN Q.EXISTS_TAC `j + (j' + 1)`
          THEN RW_TAC list_ss []
          THENL
           [Cases_on `v`
             THEN RW_TAC list_ss
                   [GT,LENGTH_RESTN_INFINITE,RESTN_FINITE,
                    IS_FINITE_def,LENGTH_RESTN,LENGTH_def,SUB]
             THEN FULL_SIMP_TAC list_ss [LENGTH_def,LS,RESTN_FINITE,xnum_11,GT]
             THEN `LENGTH(RESTN l j) = LENGTH l - j`
                   by PROVE_TAC[FinitePSLPathTheory.LENGTH_RESTN]
             THEN `j + 1 < LENGTH l` by DECIDE_TAC
             THEN `LENGTH(RESTN l (j + 1)) = LENGTH l - (j + 1)`
                   by PROVE_TAC[FinitePSLPathTheory.LENGTH_RESTN]
             THEN DECIDE_TAC,
            FULL_SIMP_TAC list_ss [ELEM_RESTN]
             THEN RW_TAC list_ss [EL_SEL_THM],
            FULL_SIMP_TAC list_ss [ELEM_RESTN]
             THEN RW_TAC list_ss [EL_SEL_THM]]]
QED

Theorem F_NEXT_CLOCK_COMP:
     !f. (!v c. F_SEM v c f = UF_SEM v (F_CLOCK_COMP c f)) ==>
         !v c. F_SEM v c (F_NEXT f) =
                UF_SEM v (F_CLOCK_COMP c (F_NEXT f))
Proof
   PROVE_TAC[F_NEXT_CLOCK_COMP_IMP1,F_NEXT_CLOCK_COMP_IMP2]
QED

Theorem F_UNTIL_CLOCK_COMP_IMP1:
     !f1 f2.
       (!v c. F_SEM v c f1 = UF_SEM v (F_CLOCK_COMP c f1))
       /\
       (!v c. F_SEM v c f2 = UF_SEM v (F_CLOCK_COMP c f2))
       ==>
       !v c. F_SEM v c (F_UNTIL(f1,f2))
             ==> UF_SEM v (F_CLOCK_COMP c (F_UNTIL(f1,f2)))
Proof
    SIMP_TAC (arith_ss++resq_SS)
       [F_SEM_def,UF_SEM_def,F_CLOCK_COMP_def,CLOCK_TICK_def]
       THEN SIMP_TAC (arith_ss++resq_SS)
             [UF_SEM_F_U_CLOCK,RESTN_RESTN,LENGTH_SEL,UF_SEM_F_AND,
              EL_SEL_LEMMA1,EL_SEL_LEMMA2,ELEM_EL]
       THEN ONCE_REWRITE_TAC
             [DECIDE ``A /\ (B /\ C) /\ D = A /\ ((A /\ B) /\ (A /\ C)) /\ D``]
       THEN SIMP_TAC (list_ss ++ resq_SS)
             [UF_SEM_RESTN_F_WEAK_BOOL_COR]
       THEN ONCE_REWRITE_TAC
             [DECIDE ``A /\ ((A /\ B) /\ (A /\ C)) /\ D = A /\ B /\ C /\ D``]
       THEN SIMP_TAC (arith_ss++resq_SS)
             [UF_SEM_def,RESTN_RESTN,UF_SEM_F_U_CLOCK,ELEM_RESTN,
              UF_SEM_F_IMPLIES,LENGTH_COMPLEMENT]
       THEN RW_TAC std_ss []
       THEN Q.EXISTS_TAC `k`
       THEN RW_TAC list_ss []
       THEN `j < LENGTH v` by PROVE_TAC[LS_TRANS_X]
       THENL
        [IMP_RES_TAC PATH_FINITE_LENGTH_RESTN_0_COR
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC arith_ss[LENGTH_def,LS],
         RES_TAC
          THEN IMP_RES_TAC RESTN_COMPLEMENT
          THEN `B_SEM (ELEM (RESTN (COMPLEMENT v) j) 0) c`
                by PROVE_TAC[]
          THEN FULL_SIMP_TAC arith_ss[ELEM_RESTN]]
QED

Theorem F_UNTIL_CLOCK_COMP_IMP2:
     !f1 f2.
       (!v c. F_SEM v c f1 = UF_SEM v (F_CLOCK_COMP c f1))
       /\
       (!v c. F_SEM v c f2 = UF_SEM v (F_CLOCK_COMP c f2))
       ==>
       !v c. UF_SEM v (F_CLOCK_COMP c (F_UNTIL(f1,f2)))
             ==> F_SEM v c (F_UNTIL(f1,f2))
Proof
    SIMP_TAC (arith_ss++resq_SS)
       [F_SEM_def,UF_SEM_def,F_CLOCK_COMP_def,CLOCK_TICK_def]
       THEN SIMP_TAC (arith_ss++resq_SS)
             [UF_SEM_F_U_CLOCK,RESTN_RESTN,LENGTH_SEL,UF_SEM_F_AND,
              EL_SEL_LEMMA1,EL_SEL_LEMMA2,ELEM_EL]
       THEN ONCE_REWRITE_TAC
             [DECIDE ``A /\ (B /\ C) /\ D = A /\ ((A /\ B) /\ (A /\ C)) /\ D``]
       THEN SIMP_TAC (list_ss ++ resq_SS)
             [UF_SEM_RESTN_F_WEAK_BOOL_COR]
       THEN ONCE_REWRITE_TAC
             [DECIDE ``A /\ ((A /\ B) /\ (A /\ C)) /\ D = A /\ B /\ C /\ D``]
       THEN SIMP_TAC (arith_ss++resq_SS)
             [UF_SEM_def,RESTN_RESTN,UF_SEM_F_U_CLOCK,ELEM_RESTN,
              UF_SEM_F_IMPLIES,LENGTH_COMPLEMENT]
       THEN RW_TAC std_ss []
       THEN Q.EXISTS_TAC `k`
       THEN RW_TAC list_ss []
       THENL
        [IMP_RES_TAC PATH_FINITE_LENGTH_RESTN_0_COR
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC arith_ss[LENGTH_def,LS],
         IMP_RES_TAC PATH_FINITE_LENGTH_RESTN_0_COR
          THEN RW_TAC std_ss []
          THEN FULL_SIMP_TAC arith_ss[LENGTH_def,LS],

         RES_TAC
          THEN `j < LENGTH v` by PROVE_TAC[LS_TRANS_X]
          THEN IMP_RES_TAC RESTN_COMPLEMENT
          THEN ASSUM_LIST
                (fn thl =>
                  ASSUME_TAC(SIMP_RULE arith_ss [GSYM(el 2 thl)] (el 5 thl)))
          THEN FULL_SIMP_TAC arith_ss[ELEM_RESTN]]
QED

Theorem F_UNTIL_CLOCK_COMP:
     !f1 f2.
       (!v c. F_SEM v c f1 = UF_SEM v (F_CLOCK_COMP c f1)) /\
       (!v c. F_SEM v c f2 = UF_SEM v (F_CLOCK_COMP c f2))
       ==>
       !v c. F_SEM v c (F_UNTIL(f1,f2)) =
              UF_SEM v (F_CLOCK_COMP c (F_UNTIL(f1,f2)))
Proof
   RW_TAC std_ss []
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [IMP_RES_TAC F_UNTIL_CLOCK_COMP_IMP1,
      IMP_RES_TAC F_UNTIL_CLOCK_COMP_IMP2]
QED

val AUX_TAC2 =
 RW_TAC (arith_ss  ++ resq_SS)
  [F_SEM_def,UF_SEM_def,F_CLOCK_COMP_def,CLOCK_TICK_def];

Theorem F_CLOCK_COMP_CORRECT:
     !f v c. F_SEM v c f = UF_SEM v (F_CLOCK_COMP c f)
Proof
   INDUCT_THEN fl_induct ASSUME_TAC
    THENL
     [(* F_STRONG_BOOL b *)
      RW_TAC std_ss [F_STRONG_BOOL_CLOCK_COMP],
      (* F_WEAK_BOOL b *)
      RW_TAC std_ss [F_WEAK_BOOL_CLOCK_COMP],
      (* F_NOT b *)
      AUX_TAC2,
      (* F_AND (f1,f2) *)
      AUX_TAC2,
      (* F_STRONG_SERE s *)
      AUX_TAC2
       THEN PROVE_TAC[S_CLOCK_COMP_CORRECT],
      (* F_WEAK_SERE s *)
      AUX_TAC2
       THEN PROVE_TAC[S_CLOCK_COMP_CORRECT],
      (* F_NEXT f *)
      RW_TAC std_ss [F_NEXT_CLOCK_COMP],
      (* F_UNTIL(f1,f2) f *)
      RW_TAC std_ss [F_UNTIL_CLOCK_COMP],
      (* F_ABORT(f,b)) *)
      AUX_TAC2,
      (* F_CLOCK(f,c) *)
      AUX_TAC2,
      (* F_SUFFIX_IMP(s,f) *)
      AUX_TAC2
       THEN PROVE_TAC[S_CLOCK_COMP_CORRECT]
     ]
QED

(* Theoem saved when compiling:
Saving theorem US_SEM_BOOL_REWRITE_LEMMA
Saving theorem S_CLOCK_COMP_CORRECT
Saving theorem fl_induct
Saving theorem LS_LE_X
Saving theorem LS_TRANS_X
Saving theorem RESTN_NIL_LENGTH
Saving theorem PATH_LENGTH_RESTN_0
Saving theorem PATH_FINITE_LENGTH_RESTN_0
Saving theorem LIST_LENGTH_RESTN_0
Saving theorem PATH_FINITE_LENGTH_RESTN_0_COR
Saving theorem UF_SEM_F_U_CLOCK
Saving theorem COMPLEMENT_LETTER_COMPLEMENT_LETTER
Saving theorem COMPLEMENT_LETTER_COMPLEMENT_LETTER_o
Saving theorem MAP_I
Saving theorem COMPLEMENT_COMPLEMENT
Saving theorem LENGTH_COMPLEMENT
Saving theorem HD_MAP
Saving theorem TL_MAP
Saving theorem RESTN_COMPLEMENT
Saving theorem RESTN_COMPLEMENT_COR
Saving theorem ELEM_COMPLEMENT
Saving theorem ELEM_COMPLEMENT_COR
Saving theorem UF_SEM_F_OR
Saving theorem UF_SEM_F_AND
Saving theorem UF_SEM_F_IMPLIES
Saving theorem UF_SEM_RESTN_F_WEAK_BOOL
Saving theorem UF_SEM_RESTN_F_WEAK_BOOL_COR
Saving theorem UF_SEM_F_F_IMP
Saving theorem UF_SEM_F_F
Saving theorem UF_SEM_F_G
Saving theorem UF_SEM_F_W_CLOCK
Saving theorem F_STRONG_BOOL_CLOCK_COMP
Saving theorem F_WEAK_BOOL_CLOCK_COMP_IMP1
Saving theorem F_WEAK_BOOL_CLOCK_COMP_IMP2
Saving theorem F_WEAK_BOOL_CLOCK_COMP
Saving theorem EL_SEL_THM
Saving theorem F_NEXT_CLOCK_COMP_IMP1
Saving theorem F_NEXT_CLOCK_COMP_IMP2
Saving theorem F_NEXT_CLOCK_COMP
Saving theorem F_UNTIL_CLOCK_COMP_IMP1
Saving theorem F_UNTIL_CLOCK_COMP_IMP2
Saving theorem F_UNTIL_CLOCK_COMP
Saving theorem F_CLOCK_COMP_CORRECT
*)
