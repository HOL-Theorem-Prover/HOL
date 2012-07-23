
open HolKernel boolLib bossLib Parse; val _ = new_theory "multiword";

val _ = set_trace "Unicode" 0;

open pred_setTheory res_quanTheory arithmeticTheory wordsLib wordsTheory bitTheory;
open pairTheory listTheory rich_listTheory relationTheory pairTheory integerTheory;
open fcpTheory;

val _ = numLib.prefer_num();

infix \\ val op \\ = op THEN;
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
val REV = Tactical.REVERSE;


(* general *)

val b2n_def = Define `(b2n T = 1) /\ (b2n F = 0:num)`;
val b2w_def = Define `b2w c = n2w (b2n c)`;

val MULT_ADD_LESS_MULT = prove(
  ``!m n k l j. m < l /\ n < k /\ j <= k ==> m * j + n < l * k:num``,
  REPEAT STRIP_TAC
  \\ `SUC m <= l` by ASM_REWRITE_TAC [GSYM LESS_EQ]
  \\ `m * k + k <= l * k` by ASM_SIMP_TAC bool_ss [LE_MULT_RCANCEL,GSYM MULT]
  \\ `m * j <= m * k` by ASM_SIMP_TAC bool_ss [LE_MULT_LCANCEL]
  \\ DECIDE_TAC);

val MULT_ADD_LESS_MULT_ADD = prove(
  ``!m n k l p. m < l /\ n < k /\ p < k ==> m * k + n < l * k + p:num``,
  REPEAT STRIP_TAC
  \\ `SUC m <= l` by ASM_REWRITE_TAC [GSYM LESS_EQ]
  \\ `m * k + k <= l * k` by ASM_SIMP_TAC bool_ss [LE_MULT_RCANCEL,GSYM MULT]
  \\ DECIDE_TAC);

val SPLIT_LET2 = prove(
  ``!x y z P. (let (x,y) = z in P x y (x,y)) =
              (let x = FST z in let y = SND z in P x y (x,y))``,
  Cases_on `z` \\ SIMP_TAC std_ss [LET_THM]);


(* multiword related general *)

val dimwords_def = Define `dimwords k n = (2:num) ** (k * dimindex n)`;

val n2mw_def = Define `
  (n2mw 0 n = []:('a word) list) /\
  (n2mw (SUC l) n = n2w n :: n2mw l (n DIV dimword(:'a)))`;

val mw2n_def = Define `
  (mw2n [] = 0) /\
  (mw2n (x::xs) = w2n (x:'a word) + dimword (:'a) * mw2n xs)`;

val mw2i_def = Define `
  (mw2i (F,xs) = (& (mw2n xs)):int) /\
  (mw2i (T,xs) = - & (mw2n xs))`;

val mw_def = tDefine "mw" `
  mw n = if n = 0 then []:'a word list else
           n2w (n MOD dimword (:'a)) :: mw (n DIV dimword(:'a))`
   (WF_REL_TAC `measure I`
    \\ SIMP_TAC std_ss [MATCH_MP DIV_LT_X ZERO_LT_dimword,ONE_LT_dimword]
    \\ DECIDE_TAC);

val mw_ind = fetch "-" "mw_ind"

val i2mw_def = Define `i2mw i = (i < 0,mw (Num (ABS i)))`;

val mw_ok_def = Define `mw_ok xs = ~(xs = []) ==> ~(LAST xs = 0w)`;

val mw_0 = prove(``(mw 0 = [])``,METIS_TAC [mw_def]);
val mw_thm = prove(
  ``~(n = 0) ==> (mw n = (n2w (n MOD dimword (:'a)):'a word) ::
                         mw (n DIV dimword(:'a)))``,
  METIS_TAC [mw_def]);

val n2mw_SUC = REWRITE_CONV [n2mw_def] ``n2mw (SUC n) m``;

val ZERO_LT_dimwords = prove(``!k. 0 < dimwords k (:'a)``,
  Cases \\ SIMP_TAC std_ss [dimwords_def,EVAL ``0<2``,ZERO_LT_EXP]);

val dimwords_SUC =
  (REWRITE_CONV [dimwords_def,MULT,EXP_ADD] THENC
   REWRITE_CONV [GSYM dimwords_def,GSYM dimword_def]) ``dimwords (SUC k) (:'a)``;

val dimwords_thm = prove(
  ``(dimwords 0 (:'a) = 1) /\
    (dimwords (SUC k) (:'a) = dimword (:'a) * dimwords k (:'a))``,
  FULL_SIMP_TAC std_ss [dimwords_def,MULT,EXP_ADD,dimword_def,AC MULT_COMM MULT_ASSOC]);

val mw_ok_CLAUSES = prove(
  ``mw_ok [] /\ (mw_ok (x::xs) = ((xs = []) ==> ~(x = 0w)) /\ mw_ok xs)``,
  SIMP_TAC std_ss [mw_ok_def,NOT_NIL_CONS]
  \\ `(xs = []) \/ ?y ys. xs = SNOC y ys` by METIS_TAC [SNOC_CASES]
  \\ ASM_SIMP_TAC std_ss [LAST_DEF,LAST_SNOC,NOT_SNOC_NIL]);

val n2mw_SNOC = store_thm("n2mw_SNOC",
  ``!k n. n2mw (SUC k) n = SNOC ((n2w (n DIV dimwords k (:'a))):'a word) (n2mw k n)``,
  Induct THEN1 REWRITE_TAC [n2mw_def,SNOC,dimwords_def,MULT_CLAUSES,EXP,DIV_1]
  \\ ONCE_REWRITE_TAC [n2mw_def] \\ ASM_REWRITE_TAC [SNOC]
  \\ SIMP_TAC bool_ss [dimwords_def,dimword_def,MULT,EXP_ADD,
       AC MULT_COMM MULT_ASSOC,DIV_DIV_DIV_MULT,EVAL ``0<2``,ZERO_LT_EXP,ZERO_LT_dimword]);

val LENGTH_n2mw = store_thm("LENGTH_n2mw",
  ``!k n. LENGTH (n2mw k n) = k``,Induct \\ ASM_REWRITE_TAC [n2mw_def,LENGTH]);

val n2mw_mod = prove(
  ``!k m. n2mw k (m MOD dimwords k (:'a)):('a word) list = n2mw k m``,
  Induct \\ REWRITE_TAC [n2mw_def,dimwords_def,MULT,CONS_11]
  \\ REWRITE_TAC [GSYM dimwords_def,EXP_ADD,GSYM dimword_def]
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ ASM_SIMP_TAC bool_ss [GSYM DIV_MOD_MOD_DIV,ZERO_LT_dimword,ZERO_LT_dimwords]
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ ASM_SIMP_TAC bool_ss [MOD_MULT_MOD,ZERO_LT_dimword,ZERO_LT_dimwords]);

val mw2n_APPEND = prove(
  ``!xs ys. mw2n (xs ++ ys) = mw2n xs + dimwords (LENGTH xs) (:'a) * mw2n (ys:'a word list)``,
  Induct \\ ASM_SIMP_TAC std_ss [dimwords_thm,LENGTH,APPEND,mw2n_def] \\ DECIDE_TAC);

val n2mw_APPEND = prove(
  ``!k l m n.
      n2mw k m ++ n2mw l n =
      n2mw (k+l) (m MOD dimwords k (:'a) + dimwords k (:'a) * n) :('a word) list``,
  Induct
  THEN1 REWRITE_TAC [n2mw_def,APPEND_NIL,ADD_CLAUSES,dimwords_def,MULT_CLAUSES,EXP,MOD_1]
  \\ ASM_REWRITE_TAC [ADD,n2mw_def,APPEND,CONS_11] \\ REPEAT STRIP_TAC THENL [
    ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM]
    \\ SIMP_TAC bool_ss [dimwords_SUC,MULT_ASSOC,n2w_11,MOD_TIMES,ZERO_LT_dimword]
    \\ ONCE_REWRITE_TAC [MULT_COMM]
    \\ SIMP_TAC bool_ss [MOD_MULT_MOD,ZERO_LT_dimword,ZERO_LT_dimwords],
    REWRITE_TAC [dimwords_SUC,DECIDE ``m+k*p*q:num=k*q*p+m``]
    \\ SIMP_TAC bool_ss [ADD_DIV_ADD_DIV,ZERO_LT_dimword,ZERO_LT_dimwords,DIV_MOD_MOD_DIV]
    \\ METIS_TAC [MULT_COMM,ADD_COMM]]);

val dimwords_ADD =
  (REWRITE_CONV [dimwords_def,RIGHT_ADD_DISTRIB,EXP_ADD] THENC
   REWRITE_CONV [GSYM dimwords_def]) ``dimwords (i+j) (:'a)``;

val TWO_dimwords_LE_dinwords_SUC = prove(
  ``!i. 2 * dimwords i (:'a) <= dimwords (SUC i) (:'a)``,
  REWRITE_TAC [dimwords_def,MULT,EXP_ADD] \\ STRIP_TAC
  \\ ASSUME_TAC (MATCH_MP LESS_OR DIMINDEX_GT_0)
  \\ Q.SPEC_TAC (`2 ** (i * dimindex (:'a))`,`x`)
  \\ IMP_RES_TAC LESS_EQUAL_ADD
  \\ ASM_REWRITE_TAC [EXP_ADD,EXP,MULT_CLAUSES,DECIDE ``n*(m*k)=m*n*k:num``]
  \\ `0 < 2**p` by ASM_REWRITE_TAC [ZERO_LT_EXP,EVAL ``0<2``]
  \\ REWRITE_TAC [RW [MULT_CLAUSES] (Q.SPECL [`m`,`1`] LE_MULT_LCANCEL)]
  \\ DECIDE_TAC);

val n2mw_MOD_ADD = prove(
  ``!i m n. n2mw i (m MOD dimwords i (:'a) + n) = n2mw i (m + n) :('a word)list``,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPEC `m` (MATCH_MP DA (Q.SPEC `i` ZERO_LT_dimwords)))
  \\ ASM_SIMP_TAC bool_ss [GSYM ADD_ASSOC,MOD_MULT]
  \\ ONCE_REWRITE_TAC [GSYM n2mw_mod]
  \\ ASM_SIMP_TAC bool_ss [MOD_TIMES,ZERO_LT_dimwords]);

val mw2n_lt = prove(
  ``!xs. mw2n xs < dimwords (LENGTH (xs:'a word list)) (:'a)``,
  Induct \\ SIMP_TAC std_ss [NOT_NIL_CONS,LENGTH,dimwords_thm,mw2n_def]
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ MATCH_MP_TAC MULT_ADD_LESS_MULT \\ ASM_SIMP_TAC std_ss [w2n_lt]);

val n2mw_EXISTS = store_thm("n2mw_EXISTS",
  ``!xs:('a word) list. ?k. (xs = n2mw (LENGTH xs) k) /\ k < dimwords (LENGTH xs) (:'a)``,
  Induct \\ REWRITE_TAC [n2mw_def,LENGTH]
  THEN1 (Q.EXISTS_TAC `0` \\ REWRITE_TAC [dimwords_def,EXP,MULT_CLAUSES] \\ EVAL_TAC)
  \\ POP_ASSUM (STRIP_ASSUME_TAC o GSYM) \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `k * dimword (:'a) + w2n h`
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ ASM_SIMP_TAC bool_ss [DIV_MULT,w2n_lt,MOD_MULT,n2w_w2n,dimwords_SUC]
  \\ MATCH_MP_TAC MULT_ADD_LESS_MULT \\ ASM_REWRITE_TAC [w2n_lt,LESS_EQ_REFL]);

val mw2n_MAP_ZERO = prove(
  ``!xs ys. mw2n (xs ++ MAP (\x.0w) ys) = mw2n xs``,
  Induct THEN1 (SIMP_TAC std_ss [APPEND] \\ Induct
    \\ FULL_SIMP_TAC std_ss [MAP,mw2n_def,w2n_n2w,ZERO_LT_dimword])
  \\ ASM_SIMP_TAC std_ss [APPEND,mw2n_def]);

val EXISTS_n2mw = prove(
  ``!(xs:'a word list).
      ?n k. (xs = n2mw k n) /\ (LENGTH xs = k) /\ n < dimwords k (:'a)``,
  Induct \\ FULL_SIMP_TAC std_ss [n2mw_def,LENGTH,CONS_11] \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `0` \\ SIMP_TAC std_ss [ZERO_LT_dimwords])
  \\ Q.EXISTS_TAC `n * dimword (:'a) + w2n h`
  \\ ASM_SIMP_TAC std_ss [MATCH_MP DIV_MULT (SPEC_ALL w2n_lt)]
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ SIMP_TAC std_ss [MATCH_MP MOD_TIMES ZERO_LT_dimword]
  \\ SIMP_TAC std_ss [n2w_mod,n2w_w2n,dimwords_thm]
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [MULT_COMM]))
  \\ ONCE_REWRITE_TAC [MULT_COMM] \\ MATCH_MP_TAC MULT_ADD_LESS_MULT
  \\ ASM_SIMP_TAC std_ss [w2n_lt]);

val mw2n_n2mw = prove(
  ``!k n. n < dimwords k (:'a) ==> (mw2n ((n2mw k n):'a word list) = n)``,
  Induct \\ SIMP_TAC std_ss [dimwords_thm,DECIDE ``n<1 = (n = 0)``,
   n2mw_def,mw2n_def,RW1[MULT_COMM](GSYM DIV_LT_X),ZERO_LT_dimwords,ZERO_LT_dimword]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ ASM_SIMP_TAC std_ss [w2n_n2w]
  \\ METIS_TAC [DIVISION,ZERO_LT_dimword,ADD_COMM,MULT_COMM]);

val mw2n_gt = prove(
  ``!xs. mw_ok xs /\ ~(xs = []) ==> dimwords (LENGTH xs - 1) (:'a) <= mw2n (xs:'a word list)``,
  Induct \\ SIMP_TAC std_ss [NOT_NIL_CONS,LENGTH,ADD1,mw2n_def]
  \\ Cases_on `xs` THEN1
   (SIMP_TAC std_ss [mw_ok_def,LAST_CONS,NOT_NIL_CONS,LENGTH,mw2n_def,dimwords_thm]
    \\ Cases_word \\ ASM_SIMP_TAC std_ss [n2w_11,w2n_n2w,ZERO_LT_dimword] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [NOT_NIL_CONS] \\ REPEAT STRIP_TAC
  \\ `mw_ok (h::t)` by FULL_SIMP_TAC std_ss [mw_ok_def,LAST_CONS,NOT_NIL_CONS]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [LENGTH,dimwords_thm,mw2n_def]
  \\ `0 < dimword (:'a)` by METIS_TAC [ZERO_LT_dimword]
  \\ `~(dimword (:'a) = 0)` by DECIDE_TAC
  \\ MATCH_MP_TAC (DECIDE ``m <= k ==> m <= n + k:num``)
  \\ ASM_SIMP_TAC std_ss [LE_MULT_LCANCEL]);

val mw2n_LESS = store_thm("mw2n_LESS",
  ``!(xs:'a word list) (ys:'a word list).
       mw_ok xs /\ mw_ok ys /\ mw2n xs <= mw2n ys ==> LENGTH xs <= LENGTH ys``,
  REPEAT STRIP_TAC \\ Cases_on `xs = []` \\ ASM_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `ys = []` THEN1
   (IMP_RES_TAC mw2n_gt
    \\ `0 < dimwords (LENGTH xs - 1) (:'a)` by FULL_SIMP_TAC std_ss [ZERO_LT_dimwords]
    \\ FULL_SIMP_TAC std_ss [LENGTH,mw2n_def] \\ DECIDE_TAC)
  \\ IMP_RES_TAC mw2n_gt
  \\ `mw2n xs < dimwords (LENGTH xs) (:'a)` by METIS_TAC [mw2n_lt]
  \\ `mw2n ys < dimwords (LENGTH ys) (:'a)` by METIS_TAC [mw2n_lt]
  \\ `dimwords (LENGTH xs - 1) (:'a) < dimwords (LENGTH ys) (:'a)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [dimwords_def] \\ DECIDE_TAC);

val mw_ok_mw = store_thm("mw_ok_mw",
  ``!n. mw_ok ((mw n):'a word list)``,
  HO_MATCH_MP_TAC mw_ind \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [mw_def]
  \\ Cases_on `n = 0` THEN1 ASM_SIMP_TAC std_ss [mw_ok_def] \\ RES_TAC
  \\ Cases_on `n < dimword (:'a)` \\ ASM_SIMP_TAC std_ss [LESS_DIV_EQ_ZERO]
  THEN1 (ONCE_REWRITE_TAC [mw_def]
    \\ ASM_SIMP_TAC std_ss [mw_ok_def,LAST_DEF,n2w_11,ZERO_LT_dimword])
  \\ FULL_SIMP_TAC std_ss [mw_ok_def,NOT_NIL_CONS,LAST_DEF]
  \\ REV (`~(mw (n DIV dimword (:'a)) = ([]:'a word list))` by ALL_TAC)
  THEN1 METIS_TAC []
  \\ `0 < n DIV dimword (:'a)` by (FULL_SIMP_TAC std_ss [X_LT_DIV,ZERO_LT_dimword] \\ DECIDE_TAC)
  \\ ONCE_REWRITE_TAC [mw_def] \\ FULL_SIMP_TAC std_ss [DECIDE ``0<n = ~(n = 0)``]
  \\ FULL_SIMP_TAC std_ss [NOT_NIL_CONS]);

val mw_ok_i2mw = store_thm("mw_ok_i2mw",
  ``!i x xs. (i2mw i = (x,xs)) ==> mw_ok xs``,
  SIMP_TAC std_ss [i2mw_def,mw_ok_mw]);

val mw_EQ_n2mw = prove(
  ``!n. mw n = n2mw (LENGTH ((mw n):'a word list)) n :'a word list``,
  HO_MATCH_MP_TAC mw_ind \\ REPEAT STRIP_TAC \\ Cases_on `n = 0`
  \\ FULL_SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [mw_def]
  \\ ASM_SIMP_TAC std_ss [LENGTH,n2mw_def,CONS_11,n2w_11,MOD_MOD,ZERO_LT_dimword]);

val LESS_dimwords_mw = prove(
  ``!n. n < dimwords (LENGTH ((mw n):'a word list)) (:'a)``,
  HO_MATCH_MP_TAC mw_ind \\ REPEAT STRIP_TAC \\ Cases_on `n = 0`
  \\ FULL_SIMP_TAC std_ss [ZERO_LT_dimwords] \\ ONCE_REWRITE_TAC [mw_def]
  \\ ASM_SIMP_TAC std_ss [LENGTH,dimwords_SUC]
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [MATCH_MP DIVISION ZERO_LT_dimword]))
  \\ MATCH_MP_TAC MULT_ADD_LESS_MULT
  \\ ASM_SIMP_TAC std_ss [ZERO_LT_dimword,MOD_LESS]);

val mw2n_mw = store_thm("mw2n_mw",
  ``!n. mw2n (mw n) = n``,
  ONCE_REWRITE_TAC [mw_EQ_n2mw] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC mw2n_n2mw \\ ASM_SIMP_TAC std_ss [LESS_dimwords_mw]);

val mw2i_i2mw = store_thm("mw2i_i2mw",
  ``!i. mw2i (i2mw i) = i``,
  REPEAT STRIP_TAC \\ Cases_on `i < 0` \\ ASM_SIMP_TAC std_ss [mw2i_def,i2mw_def]
  \\ ASM_SIMP_TAC std_ss [INT_ABS,mw2n_mw] \\ intLib.COOPER_TAC);

val mw_11 = prove(
  ``!m n. (mw m = mw n) = (m = n)``,
  HO_MATCH_MP_TAC mw_ind \\ REPEAT STRIP_TAC \\ Cases_on `m = 0` \\ Cases_on `n = 0`
  \\ ONCE_REWRITE_TAC [mw_def] \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,CONS_11]
  \\ Cases_on `m = n` \\ ASM_SIMP_TAC std_ss []
  \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword]
  \\ METIS_TAC [DIVISION,ZERO_LT_dimword]);

val i2mw_11 = store_thm("i2mw_11",
  ``!i j. (i2mw i = i2mw j) = (i = j)``,
  SIMP_TAC std_ss [i2mw_def,mw_11] \\ REPEAT STRIP_TAC
  \\ Cases_on `i = j` \\ ASM_SIMP_TAC std_ss [] \\ intLib.COOPER_TAC);

val mw_ok_IMP_EXISTS_mw = prove(
  ``!xs. mw_ok xs ==> ?n. xs = mw n``,
  Induct THEN1 METIS_TAC [mw_def] \\ SIMP_TAC std_ss [mw_ok_CLAUSES]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `n * dimword (:'a) + w2n h`
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [mw_def]))
  \\ SIMP_TAC std_ss [DIV_MULT,w2n_lt,MOD_MULT,n2w_w2n,
       MATCH_MP (DECIDE ``0<n ==> ~(n = 0)``) ZERO_LT_dimword]
  \\ Cases_on `n = 0` \\ ASM_SIMP_TAC std_ss []
  \\ `xs = []` by METIS_TAC [mw_def] \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `h <> 0w` MP_TAC \\ Q.SPEC_TAC (`h`,`h`) \\ Cases
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,w2n_n2w]);

val IMP_EQ_mw = prove(
  ``!xs i. mw_ok xs /\ (mw2n xs = i) ==> (xs = mw i)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC mw_ok_IMP_EXISTS_mw
  \\ FULL_SIMP_TAC std_ss [mw_11,mw2n_mw]);

val EXISTS_i2mw = prove(
  ``!x. mw_ok (SND x) /\ ~(x = (T,[])) ==> ?y. x = i2mw y``,
  Cases \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC mw_ok_IMP_EXISTS_mw THEN1
   (Q.EXISTS_TAC `(& n)` \\ ASM_SIMP_TAC std_ss [i2mw_def,mw_11]
    \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ intLib.COOPER_TAC)
  \\ `~(n = 0)` by METIS_TAC [mw_def]
  \\ Q.EXISTS_TAC `if q then -(& n) else (& n)` \\ POP_ASSUM MP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss [i2mw_def,mw_11]
  \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ intLib.COOPER_TAC);

val mw2i_EQ_IMP_EQ_i2mw = prove(
  ``!x. mw_ok (SND x) /\ ~(x = (T,[])) /\ (mw2i x = i) ==> (x = i2mw i)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC EXISTS_i2mw \\ FULL_SIMP_TAC std_ss [mw2i_i2mw]);

val LENGTH_mw_LESS_LENGTH_mw = prove(
  ``!m n. m <= n ==> LENGTH (mw m:'a word list) <= LENGTH (mw n:'a word list)``,
  HO_MATCH_MP_TAC mw_ind \\ REPEAT STRIP_TAC \\ Cases_on `m = 0` \\ Cases_on `n = 0`
  \\ ONCE_REWRITE_TAC [mw_def] \\ ASM_SIMP_TAC std_ss [LENGTH] THEN1 DECIDE_TAC
  \\ REV (`m DIV dimword (:'a) <= n DIV dimword (:'a)` by ALL_TAC) THEN1 METIS_TAC []
  \\ SIMP_TAC std_ss [X_LE_DIV,ZERO_LT_dimword]
  \\ MATCH_MP_TAC (DECIDE ``!p. m + p <= n ==> m <= n``)
  \\ Q.EXISTS_TAC `m MOD dimword (:'a)`
  \\ ASM_SIMP_TAC std_ss [GSYM DIVISION,ZERO_LT_dimword]);

val mw2n_EQ_IMP_EQ = prove(
  ``!xs ys. (LENGTH xs = LENGTH ys) /\ (mw2n xs = mw2n ys) ==> (xs = ys)``,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPEC `xs` EXISTS_n2mw)
  \\ STRIP_ASSUME_TAC (Q.SPEC `ys` EXISTS_n2mw)
  \\ FULL_SIMP_TAC std_ss [mw2n_n2mw]);


(* trailing and zerofix *)

val mw_trailing_def = tDefine "mw_trailing" `
  mw_trailing xs = if xs = [] then [] else
                   if LAST xs = 0w then mw_trailing (BUTLAST xs) else xs`
  (WF_REL_TAC `measure LENGTH` \\ Cases \\ SIMP_TAC std_ss [LENGTH_BUTLAST,NOT_NIL_CONS,LENGTH]);

val mw_trailing_ind = fetch "-" "mw_trailing_ind"

val mw_zerofix_def = Define `
  mw_zerofix x = if x = (T,[]) then (F,[]) else x`;

val mw_ok_mw_trailing = store_thm("mw_ok_trailing",
  ``!xs. mw_ok (mw_trailing xs)``,
  HO_MATCH_MP_TAC mw_trailing_ind \\ Cases \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [mw_trailing_def]
  \\ FULL_SIMP_TAC std_ss [mw_ok_CLAUSES,NOT_CONS_NIL]
  \\ Cases_on `LAST (h::t) = 0w` \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [mw_ok_def]);

val mw_ok_mw_trailing_ID = store_thm("mw_ok_mw_trailing_ID",
  ``!xs. mw_ok xs ==> (mw_trailing xs = xs)``,
  Cases \\ ASM_SIMP_TAC std_ss [mw_ok_def,Once mw_trailing_def,NOT_NIL_CONS]);

val mw2n_mw_trailing = prove(
  ``!xs. mw2n (mw_trailing xs) = mw2n xs``,
  HO_MATCH_MP_TAC mw_trailing_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [mw_trailing_def]
  \\ `(xs = []) \/ ?y ys. xs = SNOC y ys` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [NOT_SNOC_NIL,LAST_SNOC,FRONT_SNOC]
  \\ Cases_on `y = 0w` \\ ASM_SIMP_TAC std_ss [SNOC_APPEND]
  \\ ASM_SIMP_TAC std_ss [mw2n_APPEND,mw2n_def,w2n_n2w,ZERO_LT_dimword]);

val mw2i_mw_zerofix = prove(
  ``!x. mw2i (mw_zerofix x) = mw2i x``,
  SRW_TAC [] [mw_zerofix_def,mw2i_def,mw2n_def]);

val mw_zerofix_thm = prove(
  ``!x b xs. ~(mw_zerofix x = (T,[])) /\ mw_ok (SND (mw_zerofix (b, mw_trailing xs)))``,
  SRW_TAC [] [mw_zerofix_def,mw_ok_CLAUSES,mw_ok_mw_trailing]);

val mw_trailing_NIL = store_thm("mw_trailing_NIL",
  ``!xs. (mw_trailing xs = []) = (mw2n xs = 0)``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [mw_trailing_def]
  \\ SIMP_TAC std_ss [mw2n_def,NOT_SNOC_NIL,LAST_SNOC,FRONT_SNOC]
  \\ Cases_on `x = 0w` \\ ASM_SIMP_TAC std_ss [SNOC_APPEND,mw2n_APPEND,mw2n_def]
  \\ ASM_SIMP_TAC std_ss [w2n_n2w,ZERO_LT_dimword,GSYM SNOC_APPEND,NOT_SNOC_NIL]
  \\ `0 < dimwords (LENGTH xs) (:'a)` by METIS_TAC [ZERO_LT_dimwords] \\ DISJ2_TAC
  \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC \\ Cases_on `x`
  \\ FULL_SIMP_TAC std_ss [n2w_11,w2n_n2w,ZERO_LT_dimword]);


(* add/sub *)

val single_add_def = Define `
  single_add (x:'a word) (y:'a word) c =
    (x + y + b2w c, dimword (:'a) <= w2n x + w2n y + b2n c)`;

val mw_add_def = Define `
  (mw_add [] ys c = ([],c)) /\
  (mw_add (x::xs) ys c =
    let (z,c1) = single_add x (HD ys) c in
    let (zs,c2) = mw_add xs (TL ys) c1 in (z::zs,c2))`;

val single_sub_def = Define `
  single_sub (x:'a word) (y:'a word) c = single_add x (~y) c`;

val mw_sub_def = Define `
  (mw_sub [] ys c = ([],c)) /\
  (mw_sub (x::xs) ys c =
    let (z,c1) = single_sub x (HD ys) c in
    let (zs,c2) = mw_sub xs (TL ys) c1 in (z::zs,c2))`;

val single_add_thm = store_thm("single_add_thm",
  ``!(x:'a word) y z c d.
      (single_add x y c = (z,d)) ==>
      (w2n z + dimword (:'a) * b2n d = w2n x + w2n y + b2n c)``,
  NTAC 2 Cases_word \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_SIMP_TAC std_ss [single_add_def,w2n_n2w,LESS_MOD,b2w_def] \\ STRIP_TAC
  \\ Cases_on `dimword (:'a) <= n + n' + b2n c`
  \\ FULL_SIMP_TAC std_ss [word_add_n2w,GSYM NOT_LESS,w2n_n2w,b2n_def]
  \\ REV (`(n + n' + b2n c) DIV dimword (:'a) = 1` by ALL_TAC)
  THEN1 METIS_TAC [DIVISION,MULT_CLAUSES,ADD_COMM,ZERO_LT_dimword]
  \\ `b2n c < 2` by (Cases_on `c` \\ SIMP_TAC std_ss [b2n_def])
  \\ `n + n' + b2n c - dimword (:'a) < dimword (:'a)` by DECIDE_TAC
  \\ `n + n' + b2n c = dimword (:'a) + (n + n' + b2n c - dimword (:'a))` by DECIDE_TAC
  \\ METIS_TAC [bitTheory.DIV_MULT_1]);

val b2n_thm = prove(
  ``!c. b2n c = if c then 1 else 0``,
  Cases \\ SIMP_TAC std_ss [b2n_def]);

val single_add_eq = store_thm("single_add_eq",
  ``single_add x y c = (FST (add_with_carry (x,y:'a word,c)),
                        FST (SND (add_with_carry (x,y,c))))``,
  SIMP_TAC std_ss [single_add_def,add_with_carry_def,LET_DEF,GSYM b2n_thm]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,n2w_w2n,b2w_def]
  \\ Cases_on `x` \\ Cases_on `y` \\ ASM_SIMP_TAC std_ss [w2n_n2w,LESS_MOD]
  \\ SIMP_TAC std_ss [word_add_n2w,w2n_n2w]
  \\ Cases_on `n + n' + b2n c < dimword (:'a)`
  \\ ASM_SIMP_TAC std_ss [LESS_MOD,DECIDE ``(n <= m) = ~(m < n:num)``]
  \\ CONV_TAC ((RAND_CONV o RAND_CONV)
       (ONCE_REWRITE_CONV [MATCH_MP DIVISION ZERO_LT_dimword]))
  \\ SIMP_TAC std_ss [DECIDE ``((m = n + m:num) = (0 = n)) /\ (~(n=0)=0<n)``]
  \\ SIMP_TAC std_ss [X_LT_DIV,ZERO_LT_dimword] \\ DECIDE_TAC);

val mw_add_thm = prove(
  ``!xs ys c (zs:'a word list) d.
      (mw_add xs ys c = (zs,d)) /\ (LENGTH xs = LENGTH ys) ==>
      (mw2n zs + dimwords (LENGTH xs) (:'a) * b2n d =
       mw2n xs + mw2n ys + b2n c)``,
  Induct \\ Cases_on `ys` \\ SIMP_TAC std_ss
    [mw_add_def,LENGTH,dimwords_thm,mw2n_def,DECIDE ``~(SUC n = 0)``,HD,TL]
  \\ BasicProvers.LET_ELIM_TAC
  \\ Q.PAT_ASSUM `bb = (zs,d)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [mw2n_def]
  \\ IMP_RES_TAC single_add_thm
  \\ Q.PAT_ASSUM `!ys. bbb` (MP_TAC o RW [] o Q.SPECL [`t`,`c1`])
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC,GSYM LEFT_ADD_DISTRIB,GSYM MULT_ASSOC]
  \\ DECIDE_TAC);

val single_sub_thm = prove(
  ``!(x:'a word) y z c d.
      (single_sub x y c = (z,d)) ==>
      (w2n z + dimword (:'a) * b2n d + w2n y = w2n x + b2n c + (dimword(:'a) - 1))``,
  SIMP_TAC std_ss [single_sub_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC single_add_thm \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [DECIDE ``(x+yy+c+y=x+c+d)=(yy+y=d:num)``]
  \\ Q.SPEC_TAC (`y`,`y`) \\ Cases
  \\ `dimword (:'a) - 1 - n < dimword (:'a)` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [w2n_n2w,word_1comp_n2w] \\ DECIDE_TAC);

val mw_sub_lemma = prove(
  ``!xs ys c (zs:'a word list) d.
      (mw_sub xs ys c = (zs,d)) /\ (LENGTH xs = LENGTH ys) ==>
      (mw2n zs + mw2n ys + dimwords (LENGTH xs) (:'a) * b2n d =
       mw2n xs + b2n c + (dimwords (LENGTH xs) (:'a) - 1)) /\
      (LENGTH zs = LENGTH xs)``,
  Induct \\ Cases_on `ys` \\ SIMP_TAC std_ss
    [mw_sub_def,LENGTH,dimwords_thm,mw2n_def,DECIDE ``~(SUC n = 0)``,HD,TL]
  \\ BasicProvers.LET_ELIM_TAC \\ IMP_RES_TAC single_sub_thm
  \\ Q.PAT_ASSUM `bb = (zs,d)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [mw2n_def]
  \\ Q.PAT_ASSUM `!ys. bbb` (MP_TAC o RW [] o Q.SPECL [`t`,`c1`])
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [DECIDE ``z+d*zs+(h+d*t)+d*kk*c2 = z+h+d*zs+d*t+d*kk*c2:num``]
  \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC,GSYM LEFT_ADD_DISTRIB,GSYM MULT_ASSOC]
  \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,ADD_ASSOC,MULT_ASSOC,LENGTH]
  \\ ASM_SIMP_TAC std_ss [DECIDE ``z+h+d*xs+d*c1+dd:num = (z+d*c1+h)+d*xs+dd``]
  \\ `0 < dimwords (LENGTH t) (:'a)` by FULL_SIMP_TAC std_ss [ZERO_LT_dimwords]
  \\ Cases_on `dimwords (LENGTH t) (:'a)` \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES]
  \\ `0 < dimword (:'a)` by FULL_SIMP_TAC std_ss [ZERO_LT_dimword] \\ DECIDE_TAC);

val mw_sub_thm = prove(
  ``!xs ys c zs d.
     (LENGTH xs = LENGTH ys) /\ mw2n ys <= mw2n xs ==>
     (mw2n (FST (mw_sub xs ys T)) = mw2n xs - mw2n ys)``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC
  \\ `?zs d. mw_sub xs ys T = (zs,d)` by METIS_TAC [PAIR]
  \\ IMP_RES_TAC mw_sub_lemma \\ ASM_SIMP_TAC std_ss []
  \\ `0 < dimwords (LENGTH xs) (:'a)` by FULL_SIMP_TAC std_ss [ZERO_LT_dimwords]
  \\ Cases_on `d` \\ FULL_SIMP_TAC std_ss [b2n_def] THEN1 DECIDE_TAC
  \\ `mw2n zs + mw2n ys = mw2n xs + dimwords (LENGTH xs) (:'a)` by DECIDE_TAC
  \\ `mw2n zs < dimwords (LENGTH xs) (:'a)` by METIS_TAC [mw2n_lt]
  \\ `mw2n ys < dimwords (LENGTH xs) (:'a)` by METIS_TAC [mw2n_lt]
  \\ `F` by DECIDE_TAC);

val mw_addv_def = Define `
  (mw_addv [] ys c = if c then [1w] else []) /\
  (mw_addv (x::xs) ys c =
    let (y,ys2) = if ys = [] then (0w,ys) else (HD ys, TL ys) in
    let (z,c1) = single_add x y c in
      z :: mw_addv xs ys2 c1)`;

val WORD_NOT_ZERO_ONE = prove(
  ``~(0w = 1w)``,
  SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,ONE_LT_dimword]);

val mw_addv_thm = prove(
  ``!xs (ys:'a word list) c.
      (LENGTH ys <= LENGTH xs) ==>
      (mw2n (mw_addv xs ys c) = mw2n xs + mw2n ys + b2n c)``,
  Induct \\ Cases_on `ys` \\ SIMP_TAC std_ss [LENGTH] THEN1
   (Cases_on `c` \\ SIMP_TAC std_ss [mw_addv_def,b2n_def,
      mw2n_def,w2n_n2w,ONE_LT_dimword,mw_ok_def,LAST_DEF])
  \\ SIMP_TAC std_ss [mw_addv_def,LET_DEF] \\ REPEAT STRIP_TAC THEN1
   (POP_ASSUM (ASSUME_TAC o Q.SPEC `[]`) \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ `?z3 c3. single_add h 0w c = (z3,c3)` by METIS_TAC [PAIR]
    \\ IMP_RES_TAC single_add_thm
    \\ FULL_SIMP_TAC std_ss [mw2n_def,w2n_n2w,ZERO_LT_dimword] \\ DECIDE_TAC)
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [HD,TL,NOT_CONS_NIL]
  \\ `?z3 c3. single_add h' h c = (z3,c3)` by METIS_TAC [PAIR]
  \\ IMP_RES_TAC single_add_thm \\ FULL_SIMP_TAC std_ss [mw2n_def] \\ DECIDE_TAC);

val mw_ok_addv = prove(
  ``!xs ys c. mw_ok xs /\ mw_ok ys ==> mw_ok (mw_addv xs (ys:'a word list) c)``,
  Induct THEN1 (Cases_on `c`
    \\ SIMP_TAC std_ss [mw_addv_def,mw_ok_def,LAST_DEF,WORD_NOT_ZERO_ONE])
  \\ SIMP_TAC std_ss [mw_addv_def,SPLIT_LET2] \\ SIMP_TAC std_ss [LET_DEF]
  \\ FULL_SIMP_TAC std_ss [mw_ok_CLAUSES] \\ NTAC 4 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `ys2 = SND (if ys = [] then (0w,[]) else (HD ys,TL (ys:'a word list)))`
  \\ `mw_ok ys2` by ALL_TAC THEN1 (Q.UNABBREV_TAC `ys2`
     \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,TL,mw_ok_CLAUSES])
  \\ FULL_SIMP_TAC std_ss []
  \\ REV (Cases_on `xs`) \\ FULL_SIMP_TAC std_ss [mw_addv_def,SPLIT_LET2]
  \\ SIMP_TAC std_ss [LET_DEF,NOT_CONS_NIL]
  \\ Q.ABBREV_TAC `h2 = FST (if ys = [] then (0w,[]) else (HD ys,TL ys))`
  \\ Q.PAT_ASSUM `h <> 0w` MP_TAC \\ Q.SPEC_TAC (`h`,`h`) \\ Cases
  \\ ASM_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword]
  \\ `?z d. single_add (n2w n) h2 c = (z,d)` by METIS_TAC [PAIR]
  \\ IMP_RES_TAC single_add_thm
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [w2n_n2w]
  \\ Cases_on `d` \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL,b2n_def]
  \\ Q.SPEC_TAC (`z`,`z`) \\ Cases
  \\ ASM_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,w2n_n2w]);

val mw_addv_EQ_mw_add = store_thm("mw_addv_EQ_mw_add",
  ``!xs1 xs2 ys c1.
      (LENGTH ys = LENGTH xs1) ==>
      (mw_addv (xs1 ++ xs2) ys c1 =
        let (zs1,c2) = mw_add xs1 ys c1 in
        let (zs2,c3) = mw_add xs2 (MAP (\x.0w) xs2) c2 in
          zs1 ++ zs2 ++ if c3 then [1w] else [])``,
  Induct THEN1
   (Induct \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH,LENGTH_NIL,mw_addv_def,mw_add_def]
    THEN1 SIMP_TAC std_ss [LET_DEF,APPEND] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [MAP,HD,TL,LET_DEF] \\ Cases_on `single_add h 0x0w c1`
    \\ FULL_SIMP_TAC std_ss [APPEND]
    \\ `?ts t. mw_add xs2 (MAP (\x. 0x0w) xs2) r = (ts,t)` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss [APPEND])
  \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
  \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH,LENGTH_NIL,mw_addv_def,mw_add_def,
       NOT_NIL_CONS,LET_DEF,TL,HD] \\ REPEAT STRIP_TAC
  \\ Cases_on `single_add h' h c1` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `mw_add xs1 t r` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `mw_add xs2 (MAP (\x. 0x0w) xs2) r'`
  \\ ASM_SIMP_TAC std_ss [APPEND]);

val mw_sub2_def = Define `
  mw_sub2 xs ys zs qs c =
    let (ts,d) = mw_sub xs zs c in
    let (ts2,d2) = mw_sub ys qs d in
      (ts ++ ts2,d2)`;

val mw_sub_APPEND = prove(
  ``!xs ys zs qs c.
      (LENGTH zs = LENGTH xs) ==>
      (mw_sub (xs ++ ys) (zs ++ qs) c = mw_sub2 xs ys zs qs c)``,
  SIMP_TAC std_ss [mw_sub2_def]
  \\ Induct \\ SIMP_TAC std_ss [LENGTH,LENGTH_NIL,APPEND,mw_sub_def]
  THEN1 (BasicProvers.LET_ELIM_TAC \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [APPEND])
  \\ Cases_on `zs`
  \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``,mw_sub_def,APPEND,HD,TL]
  \\ BasicProvers.LET_ELIM_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `xx::xxx = xxxx` (ASSUME_TAC o GSYM)
  \\ Q.PAT_ASSUM `xx ++ xxx = (xxxx):'a word list` (ASSUME_TAC o GSYM)
  \\ Q.PAT_ASSUM `d' = d` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [APPEND,CONS_11]);

val mw_subv_def = Define `
  mw_subv xs ys =
    mw_trailing (FST (mw_sub2 (TAKE (LENGTH ys) xs) (DROP (LENGTH ys) xs) ys
                 (MAP (\x.0w) (DROP (LENGTH ys) xs)) T))`;

val mw_subv_thm = prove(
  ``!xs ys. mw2n ys <= mw2n xs /\ (LENGTH ys <= LENGTH xs) ==>
            (mw2n (mw_subv xs ys) = mw2n xs - mw2n ys)``,
  SIMP_TAC std_ss [mw_subv_def,mw2n_mw_trailing]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC LENGTH_TAKE
  \\ ASM_SIMP_TAC std_ss [GSYM mw_sub_APPEND,TAKE_DROP]
  \\ Q.ABBREV_TAC `zs = ys ++ MAP (\x. 0w) (DROP (LENGTH ys) xs)`
  \\ `LENGTH zs = LENGTH xs` by (Q.UNABBREV_TAC `zs`
     \\ ASM_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_MAP,LENGTH_DROP] \\ DECIDE_TAC)
  \\ `mw2n ys = mw2n zs` by (Q.UNABBREV_TAC `zs` \\ METIS_TAC [mw2n_MAP_ZERO])
  \\ FULL_SIMP_TAC std_ss [mw_sub_thm]);

val mwi_add_def = Define `
  mwi_add (s,xs) (t,ys) =
    if s = t then
      if LENGTH ys <= LENGTH xs then (s, mw_addv xs ys F) else (s, mw_addv ys xs F)
    else
      if mw2n ys = mw2n xs then (F,[]) else
      if mw2n ys <= mw2n xs then (s,mw_subv xs ys) else (~s,mw_subv ys xs)`;

val mwi_sub_def = Define `
  mwi_sub (s,xs) (t,ys) = mwi_add (s,xs) (~t,ys)`;

val mwi_add_lemma = prove(
  ``!s t xs ys.
      mw_ok xs /\ mw_ok ys ==>
      (mw2i (mwi_add (s,xs) (t,ys)) = mw2i (s,xs) + mw2i (t,ys))``,
  REPEAT STRIP_TAC \\ Cases_on `s` \\ Cases_on `t` \\ Cases_on `mw2n ys <= mw2n xs`
  \\ Cases_on `LENGTH ys <= LENGTH xs` \\ IMP_RES_TAC (DECIDE ``~(m<=n) ==> n <= m:num``)
  \\ IMP_RES_TAC mw2n_LESS \\ Cases_on `mw2n xs = mw2n ys`
  \\ IMP_RES_TAC (DECIDE ``m<=n/\~(m=n) ==> ~(n<=m:num)``)
  \\ FULL_SIMP_TAC std_ss [mwi_add_def,mw2i_def,mw_addv_thm,b2n_def,INT_ADD_CALCULATE,
       AC ADD_COMM ADD_ASSOC,mw_subv_thm,INT_ADD_REDUCE,mw2n_def]);

val mwi_add_lemma2 = RW [mw_ok_mw,GSYM i2mw_def,mw2i_i2mw]
  (Q.SPECL [`i<0:int`,`j<0:int`,`mw (Num (ABS i))`,`mw (Num (ABS j))`] mwi_add_lemma);

val mw_addv_IMP_NIL = prove(
  ``!xs ys. (mw_addv xs ys c = []) ==> (xs = [])``,
  Induct \\ SIMP_TAC std_ss [mw_addv_def,SPLIT_LET2]
  \\ SIMP_TAC std_ss [LET_DEF,NOT_CONS_NIL]);

val mw_NIL = store_thm("mw_NIL",
  ``!n. (mw n = []) = (n = 0)``,
  REPEAT STRIP_TAC \\ Cases_on `n = 0` \\ ONCE_REWRITE_TAC [mw_def]
  \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL]);

val mwi_add_thm = store_thm("mwi_add_thm",
  ``!i j. mwi_add (i2mw i) (i2mw j) = i2mw (i + j)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC mw2i_EQ_IMP_EQ_i2mw
  \\ FULL_SIMP_TAC std_ss [mwi_add_lemma2]
  \\ SIMP_TAC std_ss [mwi_add_def,i2mw_def,mw2n_mw] \\ STRIP_TAC
  THEN1 SRW_TAC [] [mw_ok_addv,mw_ok_mw,mw_subv_def,mw_ok_mw_trailing,mw_ok_CLAUSES]
  \\ SRW_TAC [] [] \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC mw_addv_IMP_NIL \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
  THEN1 (FULL_SIMP_TAC std_ss [mw_addv_def,mw_NIL] \\ intLib.COOPER_TAC)
  \\ IMP_RES_TAC (METIS_PROVE [] ``(xs = ys) ==> (mw2n xs = mw2n ys)``)
  \\ FULL_SIMP_TAC std_ss [mw2n_def]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [mw2n_mw,GSYM AND_IMP_INTRO,LENGTH_mw_LESS_LENGTH_mw]
    (Q.SPECL [`mw n`,`mw m`] mw_subv_thm))
  THEN1 (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ `Num (ABS i) <= Num (ABS j)` by intLib.COOPER_TAC
  \\ IMP_RES_TAC (SIMP_RULE std_ss [mw2n_mw,GSYM AND_IMP_INTRO,LENGTH_mw_LESS_LENGTH_mw]
    (Q.SPECL [`mw n`,`mw m`] mw_subv_thm)) \\ intLib.COOPER_TAC);

val mwi_sub_lemma = prove(
  ``!s t xs ys.
      mw_ok xs /\ mw_ok ys ==>
      (mw2i (mwi_sub (s,xs) (t,ys)) = mw2i (s,xs) - mw2i (t,ys))``,
  ASM_SIMP_TAC std_ss [mwi_add_lemma,mwi_sub_def] \\ Cases_on `t`
  \\ ASM_SIMP_TAC std_ss [mw2i_def,INT_ADD_REDUCE,INT_ADD_CALCULATE,
      INT_SUB_REDUCE,INT_SUB_CALCULATE]);

val mwi_sub_lemma2 = RW [mw_ok_mw,GSYM i2mw_def,mw2i_i2mw]
  (Q.SPECL [`i<0:int`,`j<0:int`,`mw (Num (ABS i))`,`mw (Num (ABS j))`] mwi_sub_lemma);

val mwi_sub_thm = store_thm("mwi_sub_thm",
  ``!i j. mwi_sub (i2mw i) (i2mw j) = i2mw (i - j)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC mw2i_EQ_IMP_EQ_i2mw
  \\ FULL_SIMP_TAC std_ss [mwi_sub_lemma2]
  \\ SIMP_TAC std_ss [mwi_sub_def,mwi_add_def,i2mw_def,mw2n_mw] \\ STRIP_TAC
  THEN1 SRW_TAC [] [mw_ok_addv,mw_ok_mw,mw_subv_def,mw_ok_mw_trailing,mw_ok_CLAUSES]
  \\ SRW_TAC [] [] \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC mw_addv_IMP_NIL \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
  THEN1 (FULL_SIMP_TAC std_ss [mw_addv_def,mw_NIL] \\ intLib.COOPER_TAC)
  \\ IMP_RES_TAC (METIS_PROVE [] ``(xs = ys) ==> (mw2n xs = mw2n ys)``)
  \\ FULL_SIMP_TAC std_ss [mw2n_def]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [mw2n_mw,GSYM AND_IMP_INTRO,LENGTH_mw_LESS_LENGTH_mw]
    (Q.SPECL [`mw n`,`mw m`] mw_subv_thm))
  \\ FULL_SIMP_TAC std_ss [] THEN1 DECIDE_TAC
  \\ `Num (ABS i) <= Num (ABS j)` by intLib.COOPER_TAC
  \\ IMP_RES_TAC (SIMP_RULE std_ss [mw2n_mw,GSYM AND_IMP_INTRO,LENGTH_mw_LESS_LENGTH_mw]
    (Q.SPECL [`mw n`,`mw m`] mw_subv_thm)) \\ DECIDE_TAC);


(* mul *)

val single_mul_def = Define `
  single_mul (x:'a word) (y:'a word) (c:'a word) =
    (x * y + c, n2w ((w2n x * w2n y + w2n c) DIV dimword (:'a)):'a word)`;

val single_mul_add_def = Define `
  single_mul_add p q k s =
    let (x,kc) = single_mul p q k in
    let (zs,c) = mw_add [x;kc] [s;0w] F in
      (HD zs, HD (TL zs))`;

val mw_mul_pass_def = Define `
  (mw_mul_pass x [] zs k = [k]) /\
  (mw_mul_pass x (y::ys) zs k =
    let (y1,k1) = single_mul_add x y k (HD zs) in
      y1 :: mw_mul_pass x ys (TL zs) k1)`;

val mw_mul_def = Define `
  (mw_mul [] ys zs = zs) /\
  (mw_mul (x::xs) ys zs =
    let zs2 = mw_mul_pass x ys zs 0w in
      HD zs2 :: mw_mul xs ys (TL zs2))`;

val mwi_mul_def = Define `
  mwi_mul (s,xs) (t,ys) =
    if (xs = []) \/ (ys = []) then (F,[]) else
      let (xs,ys) = (if LENGTH xs < LENGTH ys then (xs,ys) else (ys,xs)) in
        (~(s = t), mw_trailing (mw_mul xs ys (MAP (\x.0w) ys)))`;

val single_mul_thm = prove(
  ``!(x:'a word) y k z l.
      (single_mul x y k = (z,l)) ==>
      (w2n z + dimword (:'a) * w2n l = w2n x * w2n y + w2n k)``,
  NTAC 3 Cases_word \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_SIMP_TAC std_ss [single_mul_def,w2n_n2w,LESS_MOD,b2w_def]
  \\ `(n * n' + n'') DIV dimword (:'a) < dimword (:'a)` by
      (SIMP_TAC std_ss [DIV_LT_X,ZERO_LT_dimword]
       \\ MATCH_MP_TAC MULT_ADD_LESS_MULT \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss [word_add_n2w,word_mul_n2w,w2n_n2w]
  \\ METIS_TAC [DIVISION,MULT_COMM,ADD_COMM,ZERO_LT_dimword]);

val ADD_LESS_MULT = prove(
  ``!n. 1 < n ==> n + (n - 1) < n * n``,
  Induct \\ SIMP_TAC std_ss [MULT_CLAUSES] \\ REPEAT STRIP_TAC
  \\ Cases_on `1<n` \\ RES_TAC THEN1 DECIDE_TAC
  \\ `n = 1` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []);

val single_mul_add_thm = prove(
  ``!(p:'a word) q k1 k2 x1 x2.
      (single_mul_add p q k1 k2 = (x1,x2)) ==>
      (w2n x1 + dimword (:'a) * w2n x2 = w2n p * w2n q + w2n k1 + w2n k2)``,
  SIMP_TAC std_ss [single_mul_add_def] \\ BasicProvers.LET_ELIM_TAC
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC mw_add_thm \\ FULL_SIMP_TAC bool_ss [LENGTH,dimwords_thm]
  \\ FULL_SIMP_TAC std_ss [mw2n_def,w2n_n2w,ZERO_LT_dimword,b2n_def]
  \\ `?z1 z2. zs = [z1;z2]` by
   (Q.PAT_ASSUM `mw_add xss yss c = ppp` MP_TAC \\ FULL_SIMP_TAC std_ss [mw_add_def]
    \\ BasicProvers.LET_ELIM_TAC \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [HD,TL,mw2n_def]
  \\ IMP_RES_TAC single_mul_thm \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `c` \\ FULL_SIMP_TAC std_ss [b2n_def] \\ CCONTR_TAC
  \\ `dimword (:'a) * dimword (:'a) <= w2n p * w2n q + w2n k1 + w2n k2` by DECIDE_TAC
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [GSYM NOT_LESS]
  \\ `w2n p < dimword (:'a) /\ w2n k1 < dimword (:'a)` by METIS_TAC [w2n_lt]
  \\ `w2n q < dimword (:'a) /\ w2n k2 < dimword (:'a)` by METIS_TAC [w2n_lt]
  \\ `w2n p <= dimword (:'a) - 1` by DECIDE_TAC
  \\ `w2n q <= dimword (:'a) - 1` by DECIDE_TAC
  \\ `w2n p * w2n q <= (dimword (:'a) - 1) * (dimword (:'a) - 1)` by METIS_TAC [LESS_MONO_MULT2]
  \\ FULL_SIMP_TAC std_ss [LEFT_SUB_DISTRIB,RIGHT_SUB_DISTRIB,GSYM SUB_PLUS]
  \\ ASSUME_TAC (MATCH_MP ADD_LESS_MULT ONE_LT_dimword)
  \\ Q.ABBREV_TAC `d = dimword(:'a)` \\ DECIDE_TAC);

val mw_mul_pass_thm = prove(
  ``!ys zs (x:'a word) k.
      (LENGTH ys = LENGTH zs) ==>
      (mw2n (mw_mul_pass x ys zs k) = w2n x * mw2n ys + mw2n zs + w2n k) /\
      (LENGTH (mw_mul_pass x ys zs k) = LENGTH ys + 1)``,
  Induct \\ Cases_on `zs` \\ SIMP_TAC std_ss
    [mw_mul_pass_def,LENGTH,dimwords_thm,mw2n_def,DECIDE ``~(SUC n = 0)``,HD,TL]
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `t`) \\ REPEAT STRIP_TAC
  \\ BasicProvers.LET_ELIM_TAC
  \\ FULL_SIMP_TAC std_ss [mw2n_def,LEFT_ADD_DISTRIB,LENGTH,ADD1,TL]
  \\ IMP_RES_TAC single_mul_add_thm \\ DECIDE_TAC);

val mw_mul_thm = store_thm("mw_mul_thm",
  ``!xs ys (zs:'a word list).
      (LENGTH ys = LENGTH zs) ==>
      (mw2n (mw_mul xs ys zs) = mw2n xs * mw2n ys + mw2n zs)``,
  Induct \\ SIMP_TAC std_ss [mw_mul_def,mw2n_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [LET_DEF,mw2n_def]
  \\ (STRIP_ASSUME_TAC o UNDISCH o Q.SPECL [`ys`,`zs`,`h`,`0w`]) mw_mul_pass_thm
  \\ Q.ABBREV_TAC `qs = mw_mul_pass h ys zs (0w:'a word)` \\ POP_ASSUM (K ALL_TAC)
  \\ Cases_on `qs` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(0 = SUC n)``,ADD1]
  \\ FULL_SIMP_TAC std_ss [TL,HD,mw2n_def,w2n_n2w,ZERO_LT_dimword]
  \\ DECIDE_TAC);

val Num_ABS_EQ_0 = prove(
  ``!i. (Num (ABS i) = 0) = (i = 0)``,
  intLib.COOPER_TAC);

val NUM_EXISTS = prove(
  ``!i. ?n. ABS i = & n``,
  REPEAT STRIP_TAC \\ Cases_on `i < 0:int` \\ ASM_SIMP_TAC std_ss [INT_ABS]
  THEN1 (Q.EXISTS_TAC `Num (-i)` \\ intLib.COOPER_TAC)
  THEN1 (Q.EXISTS_TAC `Num i` \\ intLib.COOPER_TAC));

val mwi_mul_thm = store_thm("mwi_mul_thm",
  ``!i j. mwi_mul (i2mw i) (i2mw j) = i2mw (i * j)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [i2mw_def,mwi_mul_def,mw_NIL,Num_ABS_EQ_0]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ Cases_on `i = 0`
  THEN1 ASM_SIMP_TAC std_ss [mw_NIL,Num_ABS_EQ_0,INT_MUL_REDUCE,INT_LT_REFL]
  \\ Cases_on `j = 0`
  THEN1 ASM_SIMP_TAC std_ss [mw_NIL,Num_ABS_EQ_0,INT_MUL_REDUCE,INT_LT_REFL]
  \\ `i * j < 0 = ~(i < 0 = j < 0)` by
        (SIMP_TAC std_ss [INT_MUL_SIGN_CASES] \\ intLib.COOPER_TAC)
  \\ ASM_SIMP_TAC std_ss [] \\ SRW_TAC [] [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ MATCH_MP_TAC IMP_EQ_mw \\ ASM_SIMP_TAC std_ss [mw_ok_mw_trailing]
  \\ ASM_SIMP_TAC std_ss [mw2n_mw_trailing,LENGTH_MAP,mw_mul_thm,mw2n_mw,
       RW [APPEND,mw2n_def] (Q.SPEC `[]` mw2n_MAP_ZERO),GSYM INT_ABS_MUL]
  \\ STRIP_ASSUME_TAC (Q.SPEC `i` NUM_EXISTS)
  \\ STRIP_ASSUME_TAC (Q.SPEC `j` NUM_EXISTS)
  \\ ASM_SIMP_TAC std_ss [INT_MUL,NUM_OF_INT,AC MULT_COMM MULT_ASSOC]);


(* div by 2 *)

val mw_shift_def = Define `
  (mw_shift [] = []) /\
  (mw_shift [w] = [w >>> 1]) /\
  (mw_shift ((w:'a word)::x::xs) =
     (w >>> 1 !! x << (dimindex (:'a) - 1)) :: mw_shift (x::xs))`;

val w2n_add = prove(
  ``!x y. w2n (x + y) = (w2n x + w2n (y:'a word)) MOD dimword (:'a)``,
  REPEAT Cases \\ SIMP_TAC std_ss [word_add_n2w,w2n_n2w,MOD_PLUS,ZERO_LT_dimword]);

val word_LSL_n2w = prove(
  ``!m k. ((n2w m):'a word) << k = n2w (m * 2 ** k)``,
  SIMP_TAC std_ss [AC MULT_ASSOC MULT_COMM,WORD_MUL_LSL,word_mul_n2w]);

val mw_shift_thm = store_thm("mw_shift_thm",
  ``!xs. mw2n (mw_shift xs) = mw2n (xs:'a word list) DIV 2``,
  Induct \\ SIMP_TAC std_ss [mw_shift_def,mw2n_def]
  \\ Cases_on `xs` \\ ASM_SIMP_TAC std_ss [mw_shift_def,mw2n_def,w2n_lsr]
  \\ CONV_TAC (RAND_CONV (ALPHA_CONV ``w:'a word``)) \\ REPEAT STRIP_TAC
  \\ `w >>> 1 && h << (dimindex (:'a) - 1) = 0w` by ALL_TAC THEN1
   (SIMP_TAC std_ss [fcpTheory.CART_EQ,word_and_def,fcpTheory.FCP_BETA,
      word_lsr_def,word_lsl_def,word_0]
    \\ REPEAT STRIP_TAC \\ CCONTR_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ IMP_RES_TAC WORD_ADD_OR \\ POP_ASSUM (fn th => SIMP_TAC std_ss [GSYM th])
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Q.SPEC_TAC (`h`,`h`) \\ Q.SPEC_TAC (`w`,`w`) \\ Cases \\ Cases
  \\ ASM_SIMP_TAC std_ss [w2n_add,w2n_lsr,word_LSL_n2w,w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [dimword_def]
  \\ `0 < dimindex (:'a)` by METIS_TAC [DIMINDEX_GT_0]
  \\ `dimindex (:'a) = (dimindex (:'a) - 1) + 1` by DECIDE_TAC
  \\ Q.ABBREV_TAC `d = dimindex (:'a) - 1`
  \\ FULL_SIMP_TAC std_ss [GSYM ADD1,EXP]
  \\ SIMP_TAC std_ss [RW1 [MULT_COMM] (GSYM MOD_COMMON_FACTOR)]
  \\ `n DIV 2 + n' MOD 2 * 2 ** d < 2 * 2 ** d` by ALL_TAC THEN1
    (ONCE_REWRITE_TAC [ADD_COMM] \\ MATCH_MP_TAC MULT_ADD_LESS_MULT
     \\ FULL_SIMP_TAC std_ss [DIV_LT_X,AC MULT_COMM MULT_ASSOC])
  \\ ASM_SIMP_TAC std_ss [GSYM MULT_ASSOC]
  \\ ASM_SIMP_TAC std_ss [RW1 [ADD_COMM] (RW1 [MULT_COMM] ADD_DIV_ADD_DIV)]
  \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC,ADD_ASSOC]
  \\ `n' = n' DIV 2 * 2 + n' MOD 2` by METIS_TAC [DIVISION,DECIDE ``0<2``]
  \\ POP_ASSUM (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
  \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC,ADD_ASSOC]
  \\ SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC, AC MULT_COMM MULT_ASSOC]);

val LENGTH_mw_shift = store_thm("LENGTH_mw_shift",
  ``!xs. LENGTH (mw_shift xs) = LENGTH xs``,
  Induct \\ SIMP_TAC std_ss [LENGTH,mw_shift_def]
  \\ Cases_on `xs` \\ ASM_SIMP_TAC std_ss [LENGTH,mw_shift_def]);


(* compare *)

val mw_cmp_def = tDefine "mw_cmp" `
  mw_cmp xs ys = if xs = [] then NONE else
                 if LAST xs = LAST ys then
                   mw_cmp (BUTLAST xs) (BUTLAST ys)
                 else SOME (LAST xs <+ LAST ys)`
  (WF_REL_TAC `measure (LENGTH o FST)` \\ Cases \\ Cases
   \\ SIMP_TAC std_ss [LENGTH_BUTLAST,NOT_NIL_CONS,LENGTH])

val mw_compare_def = Define `
  mw_compare xs ys =
    if LENGTH xs < LENGTH ys then SOME (0 < 1) else
    if LENGTH ys < LENGTH xs then SOME (1 < 0) else mw_cmp xs ys`;

val option_eq_def = Define `
  (option_eq b NONE = NONE) /\
  (option_eq b (SOME x) = SOME (~(b = x)))`;

val mwi_compare_def = Define `
  mwi_compare (s,xs) (t,ys) =
    if s = t then option_eq s (mw_compare xs ys) else SOME s`;

val LAST_IMP_mw2n_LESS_mw2n = prove(
  ``!xs ys. (LENGTH xs = LENGTH ys) /\ (LAST xs <+ LAST ys) /\ ~(xs = []) ==>
            mw2n xs < mw2n ys``,
  STRIP_TAC \\ `(xs = []) \/ ?x xs1. xs = SNOC x xs1` by METIS_TAC [SNOC_CASES]
  \\ STRIP_TAC \\ `(ys = []) \/ ?y ys1. ys = SNOC y ys1` by METIS_TAC [SNOC_CASES]
  \\ ASM_SIMP_TAC std_ss [LENGTH_SNOC,LENGTH,DECIDE ``~(SUC n = 0)``,LAST_SNOC]
  \\ SIMP_TAC std_ss [SNOC_APPEND,mw2n_APPEND,mw2n_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ MATCH_MP_TAC MULT_ADD_LESS_MULT_ADD
  \\ FULL_SIMP_TAC std_ss [mw2n_lt,WORD_LO] \\ METIS_TAC [mw2n_lt]);

val mw_cmp_thm = store_thm("mw_cmp_thm",
  ``!xs ys. (LENGTH ys = LENGTH xs) ==>
            (mw_cmp xs ys = if mw2n xs = mw2n ys then NONE else
                              SOME (mw2n xs < mw2n ys))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [mw_cmp_def]
  THEN1 FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
  \\ `(ys = []) \/ ?z zs. ys = SNOC z zs` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(0 = SUC n)``,LENGTH_SNOC]
  \\ FULL_SIMP_TAC std_ss [LAST_SNOC,NOT_NIL_SNOC]
  \\ Cases_on `x = z` \\ ASM_SIMP_TAC std_ss [FRONT_SNOC]
  THEN1 ASM_SIMP_TAC std_ss [SNOC_APPEND,mw2n_APPEND]
  \\ Cases_on `x <+ z` \\ ASM_SIMP_TAC std_ss [] THEN1
   (REV (`mw2n (SNOC x xs) < mw2n (SNOC z zs)` by ALL_TAC) THEN1 DECIDE_TAC
    \\ METIS_TAC [LAST_IMP_mw2n_LESS_mw2n,LENGTH_SNOC,LAST_SNOC,NOT_NIL_SNOC])
  \\ MATCH_MP_TAC (DECIDE ``n < m ==> m <> n /\ ~(m < n:num)``)
  \\ METIS_TAC [LAST_IMP_mw2n_LESS_mw2n,LENGTH_SNOC,LAST_SNOC,NOT_NIL_SNOC,
                 WORD_LOWER_LOWER_CASES]);

val LENGTH_LESS_IMP_mw2n_LESS = store_thm("LENGTH_LESS_IMP_mw2n_LESS",
  ``!(xs:'a word list) (ys:'a word list).
      mw_ok xs /\ mw_ok ys /\ LENGTH xs < LENGTH ys ==> mw2n xs < mw2n ys``,
  REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (Q.ISPEC `ys:'a word list` SNOC_CASES)
  \\ FULL_SIMP_TAC std_ss [LENGTH,mw_ok_def,NOT_SNOC_NIL,LAST_SNOC,LENGTH_SNOC]
  \\ SIMP_TAC std_ss [SNOC_APPEND,mw2n_APPEND,mw2n_def]
  \\ Q.PAT_ASSUM `~(x = 0w)` MP_TAC \\ Q.SPEC_TAC (`x`,`x`)
  \\ Cases \\ ASM_SIMP_TAC std_ss [n2w_11,w2n_n2w,ZERO_LT_dimword]
  \\ REPEAT STRIP_TAC \\ ASSUME_TAC (Q.ISPEC `xs:'a word list` mw2n_lt)
  \\ `dimwords (LENGTH xs) (:'a) <= dimwords (LENGTH l) (:'a)` by
       (SIMP_TAC std_ss [dimwords_def] \\ DECIDE_TAC)
  \\ `0 < dimwords (LENGTH l) (:'a)` by FULL_SIMP_TAC std_ss [ZERO_LT_dimwords]
  \\ Cases_on `n` \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES] \\ DECIDE_TAC);

val mw2n_LESS_IMP_LENGTH_LESS_EQ = store_thm("mw2n_LESS_IMP_LENGTH_LESS_EQ",
  ``!xs:'a word list ys:'a word list.
      mw_ok xs /\ mw_ok ys /\ mw2n xs < mw2n ys ==> LENGTH xs <= LENGTH ys``,
  SIMP_TAC std_ss [GSYM NOT_LESS] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC LENGTH_LESS_IMP_mw2n_LESS \\ DECIDE_TAC);

val mw_compare_thm = store_thm("mw_compare_thm",
  ``!xs ys. mw_ok xs /\ mw_ok ys ==>
            (mw_compare xs ys = if mw2n xs = mw2n ys then NONE else
                                  SOME (mw2n xs < mw2n ys))``,
  REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [mw_compare_def]
  \\ Cases_on `LENGTH xs = LENGTH ys` \\ ASM_SIMP_TAC std_ss [mw_cmp_thm]
  \\ `LENGTH xs < LENGTH ys \/ LENGTH ys < LENGTH xs` by DECIDE_TAC
  \\ IMP_RES_TAC LENGTH_LESS_IMP_mw2n_LESS
  \\ IMP_RES_TAC (DECIDE ``m < n ==> ~(n < m) /\ ~(m = n:num)``)
  \\ ASM_SIMP_TAC std_ss []);

val mwi_compare_thm = store_thm("mwi_compare_thm",
  ``!i j. mwi_compare (i2mw i) (i2mw j) = if i = j then NONE else SOME (i < j)``,
  SIMP_TAC std_ss [i2mw_def,mwi_compare_def,mw_compare_thm,mw_ok_mw,mw2n_mw]
  \\ REPEAT STRIP_TAC \\ Cases_on `i = j` \\ ASM_SIMP_TAC std_ss [option_eq_def]
  \\ REV (Cases_on `i < 0 = j < 0`) \\ ASM_SIMP_TAC std_ss [] THEN1 intLib.COOPER_TAC
  \\ Cases_on `i < 0` \\ Cases_on `j < 0` \\ SRW_TAC [] [option_eq_def,INT_ABS]
  \\ intLib.COOPER_TAC);

val mw_subv_NOT_NIL = store_thm("mw_subv_NOT_NIL",
  ``!xs ys. mw_ok xs /\ mw_ok ys /\ mw2n xs < mw2n ys ==> ~(mw_subv ys xs = [])``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC mw2n_LESS_IMP_LENGTH_LESS_EQ
  \\ `mw2n xs <= mw2n ys` by DECIDE_TAC \\ IMP_RES_TAC mw_subv_thm
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [mw2n_def] \\ DECIDE_TAC);


val _ = export_theory();

