(*
  quietdec := true;
*)

open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory arithmeticTheory wordsLib wordsTheory bitTheory;
open pairTheory listTheory rich_listTheory relationTheory pairTheory;

(*
  quietdec := false;
*)

val _ = new_theory "multiword";

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val SPLIT_LET2 = prove(
  ``!x y Z P. (let (x,y) = Z in P x y (x,y)) = 
              (let x = FST Z in let y = SND Z in P x y (x,y))``,
  Cases_on `Z` \\ SIMP_TAC std_ss [LET_THM]);

val SPLIT_LET3 = prove(
  ``!x y Z P. (let (x,y,z) = Z in P x y z (x,y) (x,y,z)) = 
      (let x = FST Z in let y = FST (SND Z) in let z = SND (SND Z) in P x y z (x,y) (x,y,z))``,
  Cases_on `Z` \\ SIMP_TAC std_ss [LET_THM]);

fun EXPAND_LET_CONV thms = 
  (REWRITE_CONV thms THENC SIMP_CONV std_ss [SPLIT_LET2,SPLIT_LET3] THENC SIMP_CONV std_ss [LET_DEF]);

fun cases_thm name thms tms = 
  save_thm(name,(RW [] o foldr (uncurry CONJ) TRUTH o (map (EXPAND_LET_CONV thms))) tms);

fun cases_thm' name thms thms2 tms = 
  save_thm(name,(RW thms2 o foldr (uncurry CONJ) TRUTH o (map (EXPAND_LET_CONV thms))) tms);


(* general *)

val b2n_def = Define `(b2n T = 1) /\ (b2n F = 0)`;
val b2w_def = Define `b2w c = n2w (b2n c)`;

val b2n_thm = prove(``!c. b2n c = if c then 1 else 0``,Cases \\ REWRITE_TAC [b2n_def]);
val b2w_thm = prove(``!c. b2w c = if c then 1w else 0w``,Cases \\ REWRITE_TAC [b2w_def,b2n_def]);
val b2n_LESS = prove(``!c. b2n c <= 1``,Cases \\ REWRITE_TAC [b2n_def] \\ DECIDE_TAC);
val ONE_LE_b2n = prove(``!c. 1 <= b2n c = c``,Cases \\ REWRITE_TAC [b2n_def] \\ DECIDE_TAC);

val b2n_DIV = prove(
  ``!k. 1 < k ==> (b2n c DIV k = 0)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC LESS_DIV_EQ_ZERO 
  \\ ASSUME_TAC (Q.SPEC `c` b2n_LESS) \\ DECIDE_TAC);

val b2n_MOD = prove(
  ``!k. 1 < k ==> (b2n c MOD k = b2n c)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC LESS_MOD \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS 
  \\ Q.EXISTS_TAC `1` \\ ASM_REWRITE_TAC [b2n_LESS]);

val ONE_LESS_IMP = DECIDE ``!k. 1 < k ==> 0 < k``;

val n2w_MULT_ADD_MOD = prove(
  ``!m n. n2w (m * dimword (:'a) + n MOD dimword (:'a)) = (n2w n):'a word``,
  ONCE_REWRITE_TAC [GSYM n2w_mod] \\ SIMP_TAC bool_ss [MOD_TIMES,MOD_MOD,ZERO_LT_dimword]);

val MULT_ADD_LESS_MULT = prove(
  ``!m n k l j. m < l /\ n < k /\ j <= k ==> m * j + n < l * k:num``,
  REPEAT STRIP_TAC
  \\ `SUC m <= l` by ASM_REWRITE_TAC [GSYM LESS_EQ]
  \\ `m * k + k <= l * k` by ASM_SIMP_TAC bool_ss [LE_MULT_RCANCEL,GSYM MULT]
  \\ `m * j <= m * k` by ASM_SIMP_TAC bool_ss [LE_MULT_LCANCEL]
  \\ DECIDE_TAC);

val MULT_ADD_LESS_EQ_MULT = prove(
  ``!m n k l j. m < l /\ n <= k /\ j <= k ==> m * j + n <= l * k:num``,
  REPEAT STRIP_TAC
  \\ `SUC m <= l` by ASM_REWRITE_TAC [GSYM LESS_EQ]
  \\ `m * k + k <= l * k` by ASM_SIMP_TAC bool_ss [LE_MULT_RCANCEL,GSYM MULT]
  \\ `m * j <= m * k` by ASM_SIMP_TAC bool_ss [LE_MULT_LCANCEL]
  \\ DECIDE_TAC);

val MULT_LESS_MULT = prove(
  ``!m n k l. m < n /\ k < l ==> m * k < n * l:num``,
  REPEAT STRIP_TAC 
  \\ IMP_RES_TAC (DECIDE ``m < n ==> 0 < n``) \\ IMP_RES_TAC LESS_IMP_LESS_OR_EQ
  \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS \\ Q.EXISTS_TAC `m * l`   
  \\ ASM_SIMP_TAC bool_ss [LT_MULT_RCANCEL,RW1 [MULT_COMM] LESS_MONO_MULT]);

val ADD_MOD = prove(
  ``!k. 0 < k ==> !m n p. ((m + n) MOD k = (m + p) MOD k) = (n MOD k = p MOD k)``,
  STRIP_TAC \\ STRIP_TAC \\ Induct \\ ASM_SIMP_TAC bool_ss [ADD_CLAUSES,SUC_MOD]);

val ADD_MOD_EQ_MOD = prove(
  ``!k m n. 0 < k ==> ((n + m) MOD k = n MOD k) ==> ?p. m = p * k``,
  REPEAT STRIP_TAC
  \\ `(n + m) MOD k = (n + 0) MOD k` by ASM_REWRITE_TAC [ADD_0]
  \\ `m MOD k = 0 MOD k` by METIS_TAC [ADD_MOD]  
  \\ `?r q. (m = q * k + r) /\ r < k` by METIS_TAC [DA]
  \\ Cases_on `r` THEN1 METIS_TAC [ADD_0]
  \\ METIS_TAC [MOD_MULT,LESS_MOD,SUC_NOT]);    

val MOD_MULT_ADD_MOD = prove(
  ``!k. 0 < k ==> !m p n. (m MOD k * p + n) MOD k = (m * p + n) MOD k``,
  METIS_TAC [MOD_TIMES2,MOD_MOD,MOD_PLUS]);

val MOD_ADD_MOD = 
  (DISCH_ALL o RW [MULT_CLAUSES] o 
   Q.SPECL [`m`,`1`,`n`] o UNDISCH o Q.SPEC `k`) MOD_MULT_ADD_MOD

val ODD_NON_ZERO = prove(
  ``!k. ODD k ==> 0 < k``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC EVEN_ODD_EXISTS \\ DECIDE_TAC);


(* multiword related general *)

val dimwords_def = Define `dimwords k n = 2 ** (k * dimindex n)`;

val n2mw_def = Define `
  (n2mw 0 n = []:('a word) list) /\
  (n2mw (SUC l) n = n2w n :: n2mw l (n DIV dimword(:'a)))`;

val n2mw_SUC = REWRITE_CONV [n2mw_def] ``n2mw (SUC n) m``;

val ZERO_LT_dimwords = prove(``!k. 0 < dimwords k (:'a)``,
  Cases \\ SIMP_TAC std_ss [dimwords_def,EVAL ``0<2``,ZERO_LT_EXP]);

val dimwords_SUC = 
  (REWRITE_CONV [dimwords_def,MULT,EXP_ADD] THENC 
   REWRITE_CONV [GSYM dimwords_def,GSYM dimword_def]) ``dimwords (SUC k) (:'a)``;

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

val n2mw_APPEND = prove(
  ``!k l m n.
      n2mw k m ++ n2mw l n = 
      n2mw (k+l) (m MOD dimwords k (:'a) + dimwords k (:'a) * n) :('a word) list``,
  Induct
  THEN1 REWRITE_TAC [n2mw_def,APPEND_NIL,ADD_CLAUSES,dimwords_def,MULT_CLAUSES,EXP,MOD_1]
  \\ ASM_REWRITE_TAC [ADD,n2mw_def,APPEND,CONS_11] \\ REPEAT STRIP_TAC << [  
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

val n2mw_EXISTS = store_thm("n2mw_EXISTS",
  ``!xs:('a word) list. ?k. (xs = n2mw (LENGTH xs) k) /\ k < dimwords (LENGTH xs) (:'a)``,
  Induct \\ REWRITE_TAC [n2mw_def,LENGTH]
  THEN1 (Q.EXISTS_TAC `0` \\ REWRITE_TAC [dimwords_def,EXP,MULT_CLAUSES] \\ EVAL_TAC)
  \\ POP_ASSUM (STRIP_ASSUME_TAC o GSYM) \\ REPEAT STRIP_TAC   
  \\ Q.EXISTS_TAC `k * dimword (:'a) + w2n h`  
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ ASM_SIMP_TAC bool_ss [DIV_MULT,w2n_lt,MOD_MULT,n2w_w2n,dimwords_SUC]
  \\ MATCH_MP_TAC MULT_ADD_LESS_MULT \\ ASM_REWRITE_TAC [w2n_lt,LESS_EQ_REFL]);


(* addition *)

val single_add_def = Define `
  single_add (x:'a word) (y:'a word) c = 
    (x + y + b2w c, dimword (:'a) <= w2n x + w2n y + b2n c)`;

val mw_add_def = Define `
  (mw_add [] ys c = ([],c)) /\
  (mw_add (x::xs) (y::ys) c = 
    let (z,c1) = single_add x y c in
    let (zs,c2) = mw_add xs ys c1 in (z::zs,c2))`;

val ADD_CARRY_LEMMA = prove( 
  ``!k m. m < k + k ==> (b2n (k <= m) = m DIV k)``,
  Cases THEN1 DECIDE_TAC
  \\ REPEAT STRIP_TAC \\ Cases_on `SUC n <= m` \\ ASM_REWRITE_TAC [b2n_def] 
  \\ FULL_SIMP_TAC bool_ss [NOT_LESS_EQUAL,DIV_LT_X,LESS_DIV_EQ_ZERO]
  \\ IMP_RES_TAC LESS_EQUAL_ADD \\ FULL_SIMP_TAC bool_ss [LT_ADD_LCANCEL]
  \\ ASSUME_TAC (UNDISCH (Q.SPECL [`SUC n`,`p`] DIV_MULT))
  \\ Q.PAT_ASSUM `!q:num.b` (ASSUME_TAC o Q.SPEC `1`) 
  \\ FULL_SIMP_TAC std_ss []);

val mw_add_spec = store_thm("mw_add_spec",
  ``!i p m n c.
        mw_add (n2mw i m) ((n2mw (i + p) n):('a word) list) c = 
          (n2mw i (m + n + b2n c):('a word) list, 
           dimwords i (:'a) <= m MOD dimwords i (:'a) + n MOD dimwords i (:'a) + b2n c)``,
  Induct THEN1 
   (REWRITE_TAC [n2mw_def,mw_add_def,dimwords_def,MULT_CLAUSES,EXP,MOD_1,ADD_CLAUSES]
    \\ Cases \\ SIMP_TAC std_ss [b2n_def]) 
  \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [mw_add_def,n2mw_def,ADD]
  \\ SIMP_TAC std_ss [LET_DEF,single_add_def,CONS_11,word_add_n2w,b2w_def]
  \\ `w2n ((n2w m):'a word) + w2n ((n2w n):'a word) + b2n c < dimword (:'a) + dimword (:'a)` by 
     (MATCH_MP_TAC (DECIDE ``m < k /\ n < k /\ c <= 1 ==> m + n + c < k + k``)
      \\ Cases_on `c` \\ SIMP_TAC std_ss [b2n_def,w2n_lt])
  \\ ASM_SIMP_TAC bool_ss [ADD_CARRY_LEMMA,ZERO_LT_dimword,w2n_n2w]
  \\ ONCE_REWRITE_TAC [MATCH_MP (GSYM ADD_DIV_ADD_DIV) ZERO_LT_dimword]
  \\ SIMP_TAC bool_ss [ZERO_LT_dimword,X_LE_DIV,RIGHT_ADD_DISTRIB,ADD_ASSOC]
  \\ REWRITE_TAC [DECIDE ``md+nd+m+n+c=(md+m)+(nd+n)+c:num``]
  \\ SIMP_TAC bool_ss [ZERO_LT_dimword,GSYM DIVISION]
  \\ SIMP_TAC bool_ss [ZERO_LT_dimword,ZERO_LT_dimwords,DIV_MOD_MOD_DIV]
  \\ `(m MOD dimword (:'a) = m MOD (dimword (:'a) * dimwords i (:'a)) MOD dimword (:'a)) /\ 
      (n MOD dimword (:'a) = n MOD (dimword (:'a) * dimwords i (:'a)) MOD dimword (:'a))`
    by SIMP_TAC bool_ss [ZERO_LT_dimword,ZERO_LT_dimwords,MOD_MULT_MOD]
  \\ ASM_SIMP_TAC bool_ss [ZERO_LT_dimword,GSYM DIVISION,dimwords_SUC]
  \\ SIMP_TAC bool_ss [AC MULT_COMM MULT_ASSOC]);

val mw_add_cases = cases_thm "mw_add_cases" [mw_add_def] 
    [``FST (mw_add [] ys c)``,
     ``SND (mw_add [] ys c)``,
     ``FST (mw_add (x::xs) (y::ys) c)``,
     ``SND (mw_add (x::xs) (y::ys) c)``];  
  
val single_add_cases = cases_thm "single_add_cases" [single_add_def,b2n_thm,b2w_thm] 
    [``FST (single_add x y c)``,
     ``SND (single_add x y c)``];  


(* negation *)

val mod_neg_def = Define `
  mod_neg k n = k - 1 - n MOD k`;

val MOD_ADD_MOD_LESS_MULT = prove(
  ``!k l. 0 < k /\ 0 < l ==> !m n. n MOD l * k + m MOD k < k * l``,
  REPEAT STRIP_TAC  
  \\ `m MOD k < k` by ASM_SIMP_TAC bool_ss [GSYM DIVISION]
  \\ `SUC (n MOD l) <= l` by ASM_SIMP_TAC bool_ss [GSYM DIVISION,GSYM LESS_EQ]
  \\ `SUC (n MOD l) * k <= l * k` by (REWRITE_TAC [LE_MULT_RCANCEL] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC bool_ss [MULT] 
  \\ MATCH_MP_TAC LESS_LESS_EQ_TRANS \\ Q.EXISTS_TAC `n MOD l * k + k` 
  \\ FULL_SIMP_TAC bool_ss [AC MULT_COMM MULT_ASSOC,LT_ADD_LCANCEL]);

val mod_neg_join = store_thm("mod_neg_join",
  ``!k l. 0 < k /\ 0 < l ==> 
          !n. mod_neg (k * l) n = mod_neg l (n DIV k) * k + mod_neg k n``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [mod_neg_def,GSYM SUB_PLUS]    
  \\ REWRITE_TAC [RIGHT_SUB_DISTRIB,RIGHT_ADD_DISTRIB,EXP,MULT_CLAUSES]
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [MULT_COMM]))
  \\ REWRITE_TAC [DECIDE ``m - (k + k*n) = m - k*n - k:num``]
  \\ `SUC (n MOD k) <= k` by ASM_SIMP_TAC bool_ss [GSYM DIVISION,GSYM LESS_EQ] 
  \\ REWRITE_TAC [GSYM (ONCE_REWRITE_RULE [ADD_COMM] ADD1)]
  \\ ASM_SIMP_TAC bool_ss [DECIDE
        ``!l k n:num. n <= k ==> (l - k + (k - n) = if k <= l then l - n else k - n)``]
  \\ Cases_on `k <= k * l - k * (n DIV k) MOD l` 
  \\ ASM_SIMP_TAC bool_ss [ADD1,GSYM SUB_PLUS,ADD_ASSOC] << [
    MATCH_MP_TAC (METIS_PROVE [] ``(n = n') ==> (m - (n + 1) = m - (n' + 1))``) 
    \\ `(n DIV k) MOD l * k + n MOD k < k * l` by ASM_SIMP_TAC bool_ss [MOD_ADD_MOD_LESS_MULT]
    \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [MULT_COMM]))
    \\ Q.PAT_ASSUM `n<k*l:num` ((fn th => ONCE_REWRITE_TAC[th]) o GSYM o MATCH_MP LESS_MOD)
    \\ `0 < k * l` by ASM_REWRITE_TAC [ZERO_LESS_MULT]
    \\ ASM_SIMP_TAC bool_ss [Once (GSYM MOD_PLUS)]
    \\ ASM_SIMP_TAC bool_ss [ONCE_REWRITE_RULE [MULT_COMM] MOD_COMMON_FACTOR]
    \\ `!m. (m MOD (l*k)) MOD (k*l) = m MOD (k*l)` by METIS_TAC [MULT_COMM,MOD_MOD]
    \\ ASM_REWRITE_TAC [] \\ ASM_SIMP_TAC bool_ss [MOD_PLUS]
    \\ ASM_SIMP_TAC bool_ss [GSYM DIVISION],
    FULL_SIMP_TAC bool_ss [NOT_LESS_EQUAL]
    \\ `SUC ((n DIV k) MOD l) <= l` by ASM_SIMP_TAC bool_ss [GSYM DIVISION,GSYM LESS_EQ]
    \\ `?p. l = ((n DIV k) MOD l) + (1 + p)` 
          by ASM_REWRITE_TAC [GSYM LESS_EQ_EXISTS,ADD_ASSOC,GSYM ADD1]  
    \\ `k * l - k * (n DIV k) MOD l = k * ((1 + p) + (n DIV k) MOD l) - k * (n DIV k) MOD l` by METIS_TAC [ADD_COMM]
    \\ `k * l - k * (n DIV k) MOD l = k * (1 + p)` by METIS_TAC [LEFT_ADD_DISTRIB,ADD_SUB]  
    \\ `k + k * p < k` by METIS_TAC [LEFT_ADD_DISTRIB,MULT_CLAUSES]
    \\ METIS_TAC [DECIDE ``~(k + m < k:num)``]]);

val mw_neg_def = Define `(mw_neg [] = []) /\ (mw_neg (x:'a word ::xs) = ~x :: mw_neg xs)`;

val mod_neg_lt = store_thm("mod_neg_lt",
  ``!k n. 0 < k ==> mod_neg k n < k``,
  REWRITE_TAC [mod_neg_def] \\ REPEAT STRIP_TAC 
  \\ `n MOD k < k` by ASM_SIMP_TAC bool_ss [GSYM DIVISION] \\ DECIDE_TAC);

val mw_neg_spec = store_thm("mw_neg_spec",
  ``!i n. mw_neg (n2mw i n:('a word) list) = n2mw i (mod_neg (dimwords i (:'a)) n)``,
  Induct \\ ASM_REWRITE_TAC [n2mw_def,mw_neg_def,RW1[MULT_COMM]dimwords_SUC,CONS_11]
  \\ SIMP_TAC bool_ss [ZERO_LT_dimword,ZERO_LT_dimwords,mod_neg_join]
  \\ SIMP_TAC bool_ss [mod_neg_lt,DIV_MULT,ZERO_LT_dimword]
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod] \\ SIMP_TAC bool_ss [MOD_TIMES,ZERO_LT_dimword] 
  \\ REWRITE_TAC [mod_neg_def,word_1comp_n2w,n2w_mod]
  \\ SIMP_TAC bool_ss [MOD_MOD,ZERO_LT_dimword]);

val mod_neg_mult_MOD = prove(  
  ``!i p n. 0 < i /\ 0 < p ==> ((mod_neg (i * p) n) MOD i = mod_neg i n)``,
  SIMP_TAC bool_ss [mod_neg_join,MOD_MULT,mod_neg_lt]);


(* subtraction *)

val single_sub_def = Define `
  single_sub (x:'a word) (y:'a word) c = single_add x (~y) c`;

val mw_sub_def = Define `
  (mw_sub [] ys c = ([],c)) /\
  (mw_sub (x::xs) (y::ys) c = 
    let (z,c1) = single_sub x y c in
    let (zs,c2) = mw_sub xs ys c1 in (z::zs,c2))`;

val mw_sub_EQ_mw_add = prove(
  ``!xs:('a word) list ys c.
      (LENGTH xs <= LENGTH ys) ==> (mw_sub xs ys c = mw_add xs (mw_neg ys) c)``,
  Induct \\ REWRITE_TAC [mw_sub_def,mw_add_def] \\ STRIP_TAC \\ Cases 
  \\ REWRITE_TAC [LENGTH,DECIDE ``~(n + 1 <= 0)``,ADD1,LE_ADD_RCANCEL,mw_neg_def]
  \\ ASM_SIMP_TAC bool_ss [mw_sub_def,mw_add_def,single_sub_def]);
  
val SUB_CARRY_LEMMA = prove(
  ``!k m n c. 0 < k ==> (k <= m MOD k + mod_neg k n + b2n c = n MOD k + b2n ~c <= m MOD k)``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [mod_neg_def]
  \\ Cases_on `n MOD k + b2n ~c <= m MOD k` \\ ASM_REWRITE_TAC [GSYM SUB_PLUS] 
  \\ `n MOD k < k` by ASM_SIMP_TAC bool_ss [GSYM DIVISION]
  \\ `1 + n MOD k <= k` by DECIDE_TAC 
  \\ ASM_SIMP_TAC bool_ss [GSYM LESS_EQ_ADD_SUB]
  \\ ONCE_REWRITE_TAC [DECIDE ``k-(m+n)=k-(n+m:num)``]  
  \\ REWRITE_TAC [SUB_PLUS]
  \\ Cases_on `c` \\ FULL_SIMP_TAC bool_ss [b2n_def]
  \\ DECIDE_TAC);

val mw_sub_spec = save_thm("mw_sub_spec",let
  val th = Q.SPECL [`n2mw i m`,`n2mw (i + p) n`] mw_sub_EQ_mw_add
  val th = RW [LENGTH_n2mw,DECIDE ``i <= i + p:num``,mw_neg_spec,mw_add_spec] th
  val th = RW [dimwords_def,EXP_ADD,RIGHT_ADD_DISTRIB] th
  val th = RW1 [DECIDE ``m+n+p:num = n+(m+p)``] th
  val th = RW1 [GSYM n2mw_MOD_ADD] th
  val th = SIMP_RULE bool_ss [GSYM dimwords_def,ZERO_LT_dimwords,mod_neg_mult_MOD] th
  val th = RW1 [DECIDE ``n+(m+p) = m+n+p:num``] th
  val th = SIMP_RULE bool_ss [SUB_CARRY_LEMMA,ZERO_LT_dimwords] th
  val th = GENL [``i:num``,``p:num``,``m:num``,``n:num``] th
  in th end);

val LESS_EQ_mw_sub = prove(
  ``!k m n. 0 < k ==> n MOD k <= m MOD k ==> ((m + mod_neg k n + 1) MOD k = m MOD k - n MOD k)``,
  REPEAT STRIP_TAC
  \\ `n MOD k < k /\ m MOD k < k` by ASM_SIMP_TAC bool_ss [GSYM DIVISION]
  \\ REWRITE_TAC [mod_neg_def,GSYM SUB_PLUS] 
  \\ `1 + n MOD k <= k` by DECIDE_TAC 
  \\ REWRITE_TAC [GSYM ADD_ASSOC]
  \\ ASM_SIMP_TAC bool_ss [Once (GSYM MOD_ADD_MOD)]
  \\ ASM_SIMP_TAC bool_ss [GSYM LESS_EQ_ADD_SUB,ADD_ASSOC]
  \\ ONCE_REWRITE_TAC [DECIDE ``k-(m+n)=k-(n+m:num)``]  
  \\ REWRITE_TAC [SUB_PLUS]
  \\ `1 <= m MOD k + k - n MOD k` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [SUB_ADD]
  \\ ONCE_REWRITE_TAC [ADD_COMM]  
  \\ ASM_SIMP_TAC bool_ss [LESS_EQ_ADD_SUB,ADD_MODULUS_RIGHT]
  \\ `m MOD k - n MOD k < k` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD]);

val mw_sub_cases = cases_thm "mw_sub_cases" [mw_sub_def] 
    [``FST (mw_sub [] ys c)``,
     ``SND (mw_sub [] ys c)``,
     ``FST (mw_sub (x::xs) (y::ys) c)``,
     ``SND (mw_sub (x::xs) (y::ys) c)``];

val WORD_ADD_NEG = prove(
  ``!c x y. x + ~y + b2w c = x - y - (if c then 0w else 1w)``,
  Cases \\ REWRITE_TAC [WORD_NOT,word_sub_def,b2w_def,b2n_def,WORD_ADD_ASSOC]     
  \\ REWRITE_TAC [WORD_ADD_0,WORD_NEG_0,
       RW1[WORD_ADD_COMM]WORD_ADD_RINV,GSYM WORD_ADD_ASSOC]);

val WORD_SUB_CARRY = prove(
  ``!c x y.
      dimword (:'a) <= w2n x + w2n ~y + b2n c =
      if c then y <=+ x else dimword (:'a) <= w2n (x:'a word) + w2n ~(y:'a word)``,
  Cases \\ REWRITE_TAC [b2w_def,b2n_def,ADD_0] \\ Cases_word \\ Cases_word
  \\ `0 < dimword (:'a)` by REWRITE_TAC [ZERO_LT_dimword]
  \\ `dimword (:'a) - 1 - n' < dimword(:'a)` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD,w2n_n2w,word_ls_n2w,word_1comp_n2w]
  \\ Cases_on `n' <= n` \\ ASM_REWRITE_TAC [] THEN1 DECIDE_TAC
  \\ REWRITE_TAC [GSYM SUB_PLUS]  
  \\ ONCE_REWRITE_TAC [DECIDE ``m-(k+l)=m-(l+k:num)``]
  \\ REWRITE_TAC [SUB_PLUS,GSYM ADD_ASSOC]  
  \\ Cases_on `dimword (:'a) - n'` THEN1 `F` by DECIDE_TAC
  \\ REWRITE_TAC [ADD1,ADD_SUB] \\ REWRITE_TAC [GSYM ADD1] \\ DECIDE_TAC);

val LENGTH_FST_mw_sub = store_thm("LENGTH_FST_mw_sub",
  ``!xs ys c. (LENGTH xs = LENGTH ys) ==> (LENGTH (FST (mw_sub xs ys c)) = LENGTH xs)``,
  Induct \\ Cases_on `ys` \\ REWRITE_TAC [mw_sub_cases,LENGTH,ADD1,EQ_ADD_RCANCEL]
  THEN1 DECIDE_TAC \\ METIS_TAC []);  

val single_sub_cases = cases_thm "single_sub_cases" 
    [single_sub_def,single_add_def,WORD_ADD_NEG,WORD_SUB_CARRY] 
    [``FST (single_sub x y c)``,
     ``SND (single_sub x y c)``];
        
(* comparison *)

val mod_cmp_def = Define `
  mod_cmp k m n = (m MOD k <= n MOD k, m MOD k = n MOD k:num)`;

val mod_cmp_MOD = prove(
  ``!k. 0 < k ==> !m n c. (mod_cmp k (m MOD k) n = mod_cmp k m n) /\
                          (mod_cmp k m (n MOD k) = mod_cmp k m n)``,
  ASM_SIMP_TAC bool_ss [mod_cmp_def,MOD_MOD]);

val DIV_MULT_LESS_EQ = prove(
  ``!m n. 0 < n ==> m DIV n * n <= m``,
  METIS_TAC [LESS_EQ_ADD,DIVISION]);

val DIV_LESS_DIV_IMP_LESS = prove(
  ``!k m n. 0 < k /\ n DIV k < m DIV k ==> n < m``,
  METIS_TAC [DIV_MULT_LESS_EQ,LESS_LESS_EQ_TRANS,GSYM DIV_LT_X]);  

val LE_EQ_MOD_LE_MOD = prove(
  ``!k m n. 0<k /\ (m DIV k = n DIV k) ==> (m <= n = m MOD k <= n MOD k)``,
  METIS_TAC [DIVISION,LE_ADD_LCANCEL,num_CASES,NOT_ZERO_LT_ZERO,MULT_SUC_EQ]);

val mod_cmp_join = prove(
  ``!k l. 0 < k /\ 0 < l ==>
      (mod_cmp (k * l) m n =
        let (le1,eq1) = mod_cmp l (m DIV k) (n DIV k) in
        let (le2,eq2) = mod_cmp k m n in 
          (~eq1 /\ le1 \/ eq1 /\ le2 , eq1 /\ eq2))``,
  SIMP_TAC std_ss [mod_cmp_def,LET_DEF] \\ REPEAT STRIP_TAC << [
    Cases_on `(m DIV k) MOD l = (n DIV k) MOD l` \\ ASM_REWRITE_TAC [] << [   
      MATCH_MP_TAC ((REWRITE_RULE [AND_IMP_INTRO] o 
          SIMP_RULE bool_ss [MOD_MULT_MOD] o DISCH ``0 < l:num`` o 
          Q.SPECL [`k`,`m MOD (k * l)`,`n MOD (k * l)`]) LE_EQ_MOD_LE_MOD)
      \\ ASM_SIMP_TAC bool_ss [GSYM DIV_MOD_MOD_DIV],
      Cases_on `(m DIV k) MOD l < (n DIV k) MOD l` 
      \\ ASM_SIMP_TAC bool_ss [LESS_IMP_LESS_OR_EQ,
           DECIDE``~(m=n)/\~(m<n)==> ~(m <= n:num)``] << [      
        MATCH_MP_TAC LESS_IMP_LESS_OR_EQ
        \\ MATCH_MP_TAC DIV_LESS_DIV_IMP_LESS \\ Q.EXISTS_TAC `k`
        \\ ASM_SIMP_TAC bool_ss [GSYM DIV_MOD_MOD_DIV],        
        MATCH_MP_TAC (DECIDE ``n < m ==> ~(m <= n:num)``)
        \\ MATCH_MP_TAC DIV_LESS_DIV_IMP_LESS \\ Q.EXISTS_TAC `k`
        \\ ASM_SIMP_TAC bool_ss [GSYM DIV_MOD_MOD_DIV] \\ DECIDE_TAC]],
    EQ_TAC \\ REPEAT STRIP_TAC        
    THEN1 ASM_SIMP_TAC bool_ss [DIV_MOD_MOD_DIV]
    \\ `0 < k * l` by ASM_REWRITE_TAC [ZERO_LESS_MULT] << [
      `n = n DIV (k*l) * (k*l) + n MOD (k*l)` by ASM_SIMP_TAC bool_ss [GSYM DIVISION]
      \\ `m = m DIV (k*l) * (k*l) + m MOD (k*l)` by ASM_SIMP_TAC bool_ss [GSYM DIVISION]
      \\ ONCE_ASM_REWRITE_TAC []    
      \\ NTAC 2 (Q.PAT_ASSUM `n = n DIV (k*l) * (k*l) + n MOD (k*l)` (fn th => ALL_TAC))
      \\ `!m n k. m*(n*k) = (m*k)*n:num` by SIMP_TAC bool_ss [AC MULT_COMM MULT_ASSOC]
      \\ ASM_SIMP_TAC bool_ss [MOD_TIMES],
      `(m MOD (k * l)) DIV k = (n MOD (k * l)) DIV k` by ASM_SIMP_TAC bool_ss [GSYM DIV_MOD_MOD_DIV]
      \\ `m MOD (k * l) MOD k = n MOD (k * l) MOD k` by ASM_SIMP_TAC bool_ss [MOD_MULT_MOD]
      \\ METIS_TAC [DIVISION]]]);

val single_cmp_def = Define `
  single_cmp (x:'a word) (y:'a word) = mod_cmp (dimword (:'a)) (w2n x) (w2n y)`;

val (mw_cmp_def, mw_cmp_ind) = Defn.tprove(Hol_defn "mw_cmp" `
  (mw_cmp [] [] = (T,T)) /\
  (mw_cmp (x::xs) [] = (T,T)) /\
  (mw_cmp [] (x::xs) = (T,T)) /\
  (mw_cmp ((x:'a word)::xs) ((y:'a word)::ys) = 
    let (le1,eq1) = single_cmp (LAST (x::xs)) (LAST (y::ys)) in
      (if ~eq1 then (le1,F) else mw_cmp (BUTLAST (x::xs)) (BUTLAST (y::ys))))`,
  WF_REL_TAC `measure (LENGTH o FST)`
  \\ SIMP_TAC bool_ss [LENGTH_BUTLAST,LENGTH,NOT_CONS_NIL,
        DECIDE ``PRE (SUC n) = n``,DECIDE ``n < SUC n``]);

val mw_cmp_SNOC = store_thm("mw_cmp_SNOC",
  ``!xs ys x:'a word y:'a word.
      (LENGTH xs = LENGTH ys) ==>
      (mw_cmp (SNOC x xs) (SNOC y ys) = 
        let (le1,eq1) = single_cmp x y in (if ~eq1 then (le1,F) else mw_cmp xs ys))``,
  Cases \\ Cases \\ REWRITE_TAC [SNOC,LENGTH,DECIDE ``(SUC n = SUC m) = (n = m)``]
  \\ REWRITE_TAC [Once mw_cmp_def] \\ REWRITE_TAC [GSYM SNOC,LAST,BUTLAST]
  \\ SIMP_TAC bool_ss [mw_cmp_def,SNOC,LAST_CONS,BUTLAST_CONS,LENGTH,SUC_NOT]);

val mw_cmp_spec = store_thm("mw_cmp_spec",
  ``!i m n.
      mw_cmp (n2mw i m) ((n2mw i n):('a word) list) = 
      mod_cmp (dimwords i (:'a)) m n``,
  Induct \\ REWRITE_TAC [dimwords_def,MULT,EXP_ADD]
  THEN1 REWRITE_TAC [n2mw_def,mw_cmp_def,mod_cmp_def,MULT_CLAUSES,EXP,MOD_1,LESS_EQ_REFL]
  \\ REWRITE_TAC [GSYM dimwords_def,GSYM dimword_def,n2mw_SNOC]
  \\ SIMP_TAC bool_ss [LENGTH_n2mw,mw_cmp_SNOC]
  \\ SIMP_TAC std_ss [mod_cmp_join,ZERO_LT_dimword,ZERO_LT_dimwords]
  \\ ASM_SIMP_TAC bool_ss [single_cmp_def,w2n_n2w,mod_cmp_MOD,ZERO_LT_dimword]
  \\ SIMP_TAC std_ss [LET_DEF,mod_cmp_def,prove(
       ``(if ~eq1 then (le1,F) else (le2,eq2)) = (~eq1 /\ le1 \/ eq1 /\ le2, eq1 /\ eq2)``,
       Cases_on `eq1` \\ REWRITE_TAC [])]);


(* single-pass multiplication *)

val single_mul_def = Define `
  single_mul (x:'a word) (y:'a word) (c:'a word) = 
    (x * y + c, n2w ((w2n x * w2n y + w2n c) DIV dimword (:'a)):'a word)`;

val mw_mul_def = Define `
  (mw_mul [] y c = ([],c)) /\
  (mw_mul (x::xs) y c = 
    let (z,c1) = single_mul x y c in
    let (zs,c2) = mw_mul xs y c1 in (z::zs,c2))`;

val mw_mul_spec = store_thm("mw_mul_spec",
  ``!i m n c.
      mw_mul (n2mw i m) (y:('a word)) c = 
        (n2mw i (m * w2n y + w2n c), 
         n2w ((m MOD dimwords i (:'a) * w2n y + w2n c) DIV (dimwords i (:'a))):'a word)``,
  Induct THEN1 REWRITE_TAC [n2mw_def,mw_mul_def,dimwords_def,MULT_CLAUSES,
    EXP,MOD_1,DIV_1,ADD_CLAUSES,n2w_w2n]
  \\ ASM_SIMP_TAC std_ss [n2mw_def,mw_mul_def,LET_DEF,single_mul_def,CONS_11]  
  \\ REWRITE_TAC [GSYM word_add_n2w,GSYM word_mul_n2w,n2w_w2n]     
  \\ REWRITE_TAC [w2n_n2w] \\ NTAC 2 STRIP_TAC
  \\ `(m MOD dimword (:'a) * w2n y + w2n c) DIV dimword (:'a) < dimword (:'a)` by ALL_TAC << [    
    SIMP_TAC bool_ss [ZERO_LT_dimword,DIV_LT_X]
    \\ MATCH_MP_TAC MULT_ADD_LESS_MULT
    \\ SIMP_TAC bool_ss [GSYM DIVISION,ZERO_LT_dimword,w2n_lt,LESS_IMP_LESS_OR_EQ],    
    ASM_SIMP_TAC bool_ss [LESS_MOD,GSYM ADD_DIV_ADD_DIV,ZERO_LT_dimword]
    \\ SIMP_TAC bool_ss [ZERO_LT_dimword,ZERO_LT_dimwords,DIV_DIV_DIV_MULT]
    \\ REWRITE_TAC [DECIDE ``md*y*d+(m*y+c)=(md*d*y+m*y)+c:num``]
    \\ REWRITE_TAC [GSYM RIGHT_ADD_DISTRIB]
    \\ SIMP_TAC bool_ss [GSYM DIVISION,ZERO_LT_dimword,RW1[MULT_COMM]dimwords_SUC]
    \\ SIMP_TAC bool_ss [DIV_MOD_MOD_DIV,ZERO_LT_dimword,ZERO_LT_dimwords] 
    \\ `(m MOD dimword (:'a) = m MOD (dimword (:'a) * dimwords i (:'a)) MOD dimword (:'a))`
      by SIMP_TAC bool_ss [ZERO_LT_dimword,ZERO_LT_dimwords,MOD_MULT_MOD]
    \\ ASM_SIMP_TAC bool_ss [GSYM DIVISION,ZERO_LT_dimword]]);

val mw_mul_cases = cases_thm "mw_mul_cases" [mw_mul_def] 
    [``FST (mw_mul [] y k)``,``SND (mw_mul [] y k)``,
     ``FST (mw_mul (x::xs) y k)``,``SND (mw_mul (x::xs) y k)``];

val single_mul_cases = cases_thm "single_mul_cases" [single_mul_def]
    [``FST (single_mul x y c)``,
     ``SND (single_mul x y c)``];  

val ZERO_concat_n2w = prove(
  ``(0w:word32 @@ ((n2w n):word32)):word64 = n2w (n MOD dimword (:32))``,
  SIMP_TAC std_ss [word_concat_def,word_join_def,LET_DEF,w2w_def,word_lsl_n2w] 
  \\ REWRITE_TAC [EVAL ``dimindex (:32 + 32) < 1 + dimindex (:32)``,word_0_n2w]    
  \\ REWRITE_TAC [MULT_CLAUSES,WORD_OR_CLAUSES,w2n_n2w,dimword_def] 
  \\ REWRITE_TAC [EVAL ``dimindex (:32 + 32)``]    
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod] 
  \\ REWRITE_TAC [EVAL ``dimindex (:64)``,dimword_def]
  \\ SIMP_TAC bool_ss [MOD_MOD,EVAL ``0 < 2**64``]);
  
val ZERO_concat_ZERO = store_thm("ZERO_concat_ZERO",
  ``(0w:word32) @@ (0w:word32) = 0w:word64``,
  SIMP_TAC bool_ss [ZERO_concat_n2w,ZERO_LT_dimword,LESS_MOD]);

val single_mul_cases32 = store_thm("single_mul_cases32",
  ``!x:word32 y:word32 c:word32.
      (FST (single_mul x y c) = (31 >< 0) ((0w:word32) @@ c + w2w x * (w2w y):word64)) /\
      (SND (single_mul x y c) = (63 >< 32) ((0w:word32) @@ c + w2w x * (w2w y):word64))``,
  NTAC 3 Cases_word 
  \\ ASM_SIMP_TAC std_ss [w2w_def,w2n_n2w,LESS_MOD,single_mul_def,
      LET_DEF,word_mul_n2w,n2w_mod,ZERO_concat_n2w,word_add_n2w]
  \\ SIMP_TAC std_ss [word_extract_def,word_bits_n2w,
       EVAL ``MIN 31 (dimindex (:64) - 1)``,EVAL ``MIN 63 (dimindex (:64) - 1)``] 
  \\ REWRITE_TAC [BITS_def,MOD_2EXP_def,DIV_2EXP_def,EXP,DIV_1,w2w_def]
  \\ REWRITE_TAC [w2n_n2w,n2w_11,dimword_def,EVAL ``SUC 31 - 0``,EVAL ``SUC 63 - 32``,
       EVAL ``dimindex (:64)``,EVAL ``dimindex (:32)``,GSYM (EVAL ``32+32``)]
  \\ SIMP_TAC bool_ss [EVAL ``0 < 2**32``,EXP_ADD,MOD_MULT_MOD,MOD_MOD]
  \\ METIS_TAC [ADD_COMM]);


(* multiplication *)

val mw_add_mul_def = Define `mw_add_mul x ys zs = FST (mw_add zs (FST (mw_mul ys x 0w)) F)`;

val mw_long_mul_def = Define `
  (mw_long_mul [] ys zs = zs) /\
  (mw_long_mul (x::xs) ys zs = 
    let zs' = mw_add_mul x ys zs in 
      HD zs' :: mw_long_mul xs ys (TL zs'))`;

val mw_add_mul_spec = save_thm("mw_add_mul_spec",
  REWRITE_CONV [mw_add_mul_def,word_0_n2w,b2n_def,ADD_0,FST,mw_mul_spec,mw_add_spec] 
    ``mw_add_mul x (n2mw (i+p) m) (n2mw i n)``);

val mw_add_mul_spec_simple = RW [ADD_0] (Q.INST [`p`|->`0`] mw_add_mul_spec);

val mw_long_mul_spec = store_thm("mw_long_mul_spec",
  ``!i j p m n r. 
        mw_long_mul (n2mw i m) (n2mw (i+j+p) n) (n2mw (i+j) r) = 
        n2mw (i+j) (m MOD dimwords i (:'a) * n + r):('a word) list``,
  Induct THEN1 REWRITE_TAC [mw_long_mul_def,n2mw_def,
               dimwords_def,MULT_CLAUSES,EXP,MOD_1,ADD_CLAUSES]
  \\ REPEAT STRIP_TAC \\ REWRITE_TAC [n2mw_def,mw_long_mul_def]
  \\ SIMP_TAC std_ss [mw_add_mul_spec,LET_DEF,w2n_n2w]
  \\ SIMP_TAC std_ss [ADD,n2mw_def,HD,TL,CONS_11]
  \\ ASM_REWRITE_TAC [GSYM n2mw_def,ADD1,DECIDE ``k+l+p+1=k+l+(p+1)``]  
  \\ ASSUME_TAC ZERO_LT_dimword \\ ASSUME_TAC ZERO_LT_dimwords \\ STRIP_TAC << [
    REWRITE_TAC [GSYM ADD1,RW1[MULT_COMM]dimwords_SUC]    
    \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ ONCE_REWRITE_TAC [MATCH_MP (GSYM MOD_MULT_ADD_MOD) ZERO_LT_dimword]
    \\ SIMP_TAC bool_ss [MOD_MULT_MOD,ZERO_LT_dimword,ZERO_LT_dimwords]
    \\ SIMP_TAC bool_ss [AC ADD_COMM ADD_ASSOC, AC MULT_COMM MULT_ASSOC],
    ASM_SIMP_TAC bool_ss [DIV_MOD_MOD_DIV,GSYM ADD_DIV_ADD_DIV,ADD_ASSOC]
    \\ ONCE_REWRITE_TAC [DECIDE ``m*n*d+r+n*mm = m*d*n+mm*n+r:num``]
    \\ REWRITE_TAC [GSYM RIGHT_ADD_DISTRIB]
    \\ `(m MOD dimword (:'a) = m MOD (dimword (:'a) * dimwords i (:'a)) MOD dimword (:'a))`
      by SIMP_TAC bool_ss [ZERO_LT_dimword,ZERO_LT_dimwords,MOD_MULT_MOD]
    \\ ASM_SIMP_TAC bool_ss [GSYM DIVISION,ZERO_LT_dimword]
    \\ REWRITE_TAC [GSYM ADD1,RW1[MULT_COMM]dimwords_SUC]]);


(* Montgomery multiplication lemmas *)

val montgomery_vars_def = Define `
  montgomery_vars n n' r r' = (n * n' = r * r' - 1) /\ ODD n /\ 0 < n' /\ n < r`;

val residue_def = Define `residue p r n = (p * r) MOD n`;

val MULT_2EXP_MOD_IMP_MOD = prove(
  ``!k. ODD k ==> 
      !m n l. ((m * 2 ** l) MOD k = (n * 2 ** l) MOD k) ==> (m MOD k = n MOD k)``,
  NTAC 4 STRIP_TAC \\ Induct 
  \\ REWRITE_TAC [ONCE_REWRITE_RULE [MULT_COMM] EXP,MULT_CLAUSES,MULT_ASSOC]
  \\ EVERY_ASSUM (UNDISCH_TAC o concl) 
  \\ Q.SPEC_TAC (`m*2**l`,`m'`) \\ Q.SPEC_TAC (`n*2**l`,`n'`)
  \\ ONCE_REWRITE_TAC [MULT_COMM] \\ REPEAT STRIP_TAC 
  \\ STRIP_ASSUME_TAC (Q.SPECL [`m'`,`n'`] LESS_EQ_CASES)
  \\ IMP_RES_TAC LESS_EQUAL_ADD \\ IMP_RES_TAC ODD_NON_ZERO 
  \\ FULL_SIMP_TAC bool_ss [LEFT_ADD_DISTRIB,GSYM ADD1]
  \\ IMP_RES_TAC ADD_MOD_EQ_MOD \\ IMP_RES_TAC 
   (ONCE_REWRITE_RULE [METIS_PROVE [] ``(g = n MOD k) = (n MOD k = g)``] ADD_MOD_EQ_MOD)
  \\ `EVEN p'` by METIS_TAC [ODD_EVEN,EVEN_MULT,EVEN_DOUBLE]
  \\ IMP_RES_TAC EVEN_ODD_EXISTS \\ FULL_SIMP_TAC bool_ss 
       [RW1 [ADD_COMM] MOD_TIMES,EQ_MULT_LCANCEL,EVAL ``2=0``,GSYM MULT_ASSOC]);

val MONTGOMERY_LEMMA = prove(
  ``((t + m * n) MOD 2**l = 0) ==>
    ODD n ==> 0 < n' ==> (n * n' = 2**l * r' - 1) ==>
    (((t + m * n) DIV 2**l) MOD n = (t * r') MOD n)``,
  REPEAT STRIP_TAC
  \\ `0 < 2**l` by REWRITE_TAC [ZERO_LT_EXP,EVAL ``0 < 2``]
  \\ `0 < n * n' /\ 0 < n` by ASM_SIMP_TAC bool_ss [ZERO_LESS_MULT,ODD_NON_ZERO]
  \\ `0 < r'` by (Cases_on `r' = 0` \\
      FULL_SIMP_TAC bool_ss [MULT_CLAUSES,EVAL ``0-1``,MULT_EQ_0] \\ DECIDE_TAC)
  \\ IMP_RES_TAC MULT_2EXP_MOD_IMP_MOD
  \\ Q.PAT_ASSUM `!k.m` MATCH_MP_TAC \\ Q.EXISTS_TAC `l`
  \\ `(t + m * n) DIV 2 ** l * 2 ** l = t + m * n` by METIS_TAC [DIVISION,ADD_0]
  \\ ASM_SIMP_TAC bool_ss []
  \\ ONCE_REWRITE_TAC [ADD_COMM] \\ ASM_SIMP_TAC bool_ss [MOD_TIMES]
  \\ `r' * 2**l = n' * n + 1` by DECIDE_TAC
  \\ Q.PAT_ASSUM `n = m - 1` (fn th => ALL_TAC)
  \\ ASM_REWRITE_TAC [GSYM MULT_ASSOC]
  \\ ASM_SIMP_TAC bool_ss [MULT_ASSOC,LEFT_ADD_DISTRIB,MULT_CLAUSES,MOD_TIMES]);

val residue_MULT = store_thm("residue_MULT",
  ``!n n' r r' p q.
      montgomery_vars n n' r r' ==>
      ((residue p r n * residue q r n * r') MOD n = residue (p * q) r n)``,
  REWRITE_TAC [residue_def,montgomery_vars_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC ODD_NON_ZERO
  \\ ASM_SIMP_TAC bool_ss [Once (GSYM MOD_TIMES2)]
  \\ `((p * r) MOD n * (q * r) MOD n) MOD n = ((p * r)*(q * r)) MOD n` by 
      ASM_SIMP_TAC bool_ss [MOD_TIMES2] \\ ASM_REWRITE_TAC []
  \\ ASM_SIMP_TAC bool_ss [MOD_TIMES2,GSYM MULT_ASSOC]
  \\ `0 < n * n'` by ASM_REWRITE_TAC [ZERO_LESS_MULT]    
  \\ `r * r' = n * n' + 1` by DECIDE_TAC
  \\ Q.PAT_ASSUM `n*n' =r*r'-1` (fn th => ALL_TAC)
  \\ ASM_REWRITE_TAC [] \\ ONCE_REWRITE_TAC [METIS_PROVE [MULT_COMM] ``n*n'+1=n'*n+1``]
  \\ ASM_SIMP_TAC bool_ss [MULT_ASSOC,LEFT_ADD_DISTRIB,MULT_CLAUSES,MOD_TIMES]
  \\ METIS_TAC [MULT_COMM,MULT_ASSOC]);

val residue_LT = store_thm("residue_LT",
  ``!n n' r r' p. montgomery_vars n n' r r' ==> residue p r n < n``,
  REWRITE_TAC [montgomery_vars_def,residue_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC ODD_NON_ZERO \\ ASM_SIMP_TAC bool_ss [GSYM DIVISION]);

val imp_montgomery_vars = prove(
  ``(r * r' - n * n' = 1) /\ n < r /\ EVEN r ==> montgomery_vars n n' r r'``,
  REWRITE_TAC [montgomery_vars_def] \\ REPEAT STRIP_TAC \\ REPEAT DECIDE_TAC 
  \\ REWRITE_TAC [ODD_EVEN] \\ CCONTR_TAC \\ `ODD 1` by EVAL_TAC 
  \\ FULL_SIMP_TAC bool_ss [DECIDE ``~(0<n) = (n = 0)``] << [
    `(?m. r = 2 * m) /\ (?p. n = 2 * p)` by METIS_TAC [EVEN_EXISTS]
    \\ `2 * m * r' - 2 * p * n' = 1` by METIS_TAC []
    \\ FULL_SIMP_TAC bool_ss [GSYM LEFT_SUB_DISTRIB,GSYM MULT_ASSOC]
    \\ METIS_TAC [EVEN_AND_ODD,EVEN_DOUBLE],
    `?m. r = 2 * m` by METIS_TAC [EVEN_EXISTS]
    \\ Cases_on `n'` \\ REPEAT DECIDE_TAC
    \\ FULL_SIMP_TAC bool_ss [MULT_CLAUSES,SUB_0,GSYM MULT_ASSOC]
    \\ METIS_TAC [EVEN_AND_ODD,EVEN_DOUBLE]]);


(* Montgomery multiplication - basic implementation *)

val montprod_vars_def = Define `
  montprod_vars n n' r r' t u = 
    montgomery_vars n n' r r' /\ t <= n /\ u < r`;

val mw_monmult_def = Define `
  (mw_monmult [] ys ns m zs = zs) /\
  (mw_monmult (x::xs) ys ns m zs =  
    let u = (x * HD ys + HD zs) * m in
    let zs = mw_add_mul x ys (zs ++ [0w]) in
    let zs = mw_add_mul u ns zs  in
      HD zs :: mw_monmult xs ys ns m (TL zs))`;

val mw_monmult2_def = Define `
  (mw_monmult2 [] ys ns m zs = zs) /\
  (mw_monmult2 (x::xs) ys ns m zs =  
    let u = (x * HD ys + HD zs) * m in
    let zs = mw_add_mul x ys (zs ++ [0w]) in
    let zs = mw_add_mul u ns zs in
      mw_monmult2 xs ys ns m (TL zs))`;

val mw_monprod_def = Define `
  mw_monprod xs ys ns m zs = 
    let zs = mw_monmult2 xs ys ns m zs in
    let (zs',c) = mw_sub zs ns T in
      (if c then zs' else zs)`;

val mw_monmult2_EQ_mw_monmult = prove(
  ``!xs ys ns m zs. 
      mw_monmult2 xs ys ns m zs = BUTFIRSTN (LENGTH xs) (mw_monmult xs ys ns m zs)``,
  Induct \\ REWRITE_TAC [BUTFIRSTN,LENGTH,mw_monmult_def,mw_monmult2_def]
  \\ ASM_SIMP_TAC bool_ss [LET_DEF,BUTFIRSTN]);

val BUTFIRSTN_n2mw = prove(
  ``!k n p. BUTFIRSTN k (n2mw (k + p) n) = n2mw p (n DIV dimwords k (:'a)): ('a word) list``,
  Induct THEN1 REWRITE_TAC [BUTFIRSTN,dimwords_def,MULT_CLAUSES,EXP,DIV_1,ADD_CLAUSES]    
  \\ ASM_REWRITE_TAC [ADD_CLAUSES,n2mw_def,BUTFIRSTN]
  \\ SIMP_TAC bool_ss [DIV_DIV_DIV_MULT,ZERO_LT_dimwords,ZERO_LT_dimword]
  \\ REWRITE_TAC [RW1 [MULT_COMM] dimwords_SUC]);
  
val BOUND_LEMMA = prove(
  ``j <= i /\ i < N /\ m < d /\ n < d /\ k < 2 * d ==>
    i * n + j * m + k < 2 * d * N``,
  REPEAT STRIP_TAC  
  \\ `SUC i <= N` by ASM_REWRITE_TAC [GSYM LESS_EQ]
  \\ `SUC i * (2 * d) <= N * (2 * d)` by ASM_REWRITE_TAC [LE_MULT_RCANCEL]
  \\ FULL_SIMP_TAC bool_ss [MULT]
  \\ `i * d + i * d + k < 2 * d * N` by DECIDE_TAC
  \\ `i * n <= i * d` by ASM_SIMP_TAC bool_ss [LE_MULT_LCANCEL,LESS_IMP_LESS_OR_EQ]
  \\ `i * m <= i * d` by ASM_SIMP_TAC bool_ss [LE_MULT_LCANCEL,LESS_IMP_LESS_OR_EQ]
  \\ `j * m <= i * m` by ASM_SIMP_TAC bool_ss [LE_MULT_RCANCEL]
  \\ `j * m <= i * d` by METIS_TAC [LESS_EQ_TRANS]
  \\ `i * n + j * m <= i * d + i * d` by METIS_TAC [DECIDE ``m<=k /\ n<=l ==> m+n<=k+l:num``]
  \\ IMP_RES_TAC (DECIDE ``m + k < r ==> n <= m ==> n + k < r:num``));

val BOUNDS = prove(
  ``i < N /\ j < N /\ m < d /\ n < d /\ k < 2 * d ==> i * n + j * m + k < 2 * d * N``,
  REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPECL [`j`,`i`] LESS_EQ_CASES)
  \\ ASM_SIMP_TAC bool_ss [BOUND_LEMMA]
  \\ ONCE_REWRITE_TAC [DECIDE ``i+j+k=j+i+k:num``] \\ ASM_SIMP_TAC bool_ss [BOUND_LEMMA]);

val mw_monpro1_spec_lemma = prove(
  ``!i p t n q r. 
     r < 2*dimwords (i+p-1) (:'a) /\ n < dimwords (i+p-1) (:'a) /\ 
     u < dimwords (i+p-1) (:'a) ==>
     ?m. m < dimwords i (:'a) /\
       (mw_monmult (n2mw i t) (n2mw (i+p+1) u) (n2mw (i+p+1) n) (n2w q) (n2mw (i+p) r) = 
        n2mw (i+i+p) (t MOD dimwords i (:'a) * u + r + m * n):('a word)list)``,
  Induct \\ REPEAT STRIP_TAC THEN1    
    (Q.EXISTS_TAC `0` 
     \\ REWRITE_TAC [mw_monmult_def,MULT_CLAUSES,ADD_0,ZERO_LT_dimwords,n2mw_def]
     \\ REWRITE_TAC [dimwords_def,MULT_CLAUSES,EXP,MOD_1,DIV_1,ADD_CLAUSES])
  \\ REWRITE_TAC [mw_monmult_def,ADD,HD,n2mw_def]
  \\ REWRITE_TAC [GSYM n2mw_SUC,GSYM (REWRITE_CONV [n2mw_def] ``n2mw (SUC 0) 0``),n2mw_APPEND]
  \\ REWRITE_TAC [MULT_CLAUSES,ADD_0,ADD_CLAUSES,GSYM ADD1]   
  \\ `2 * dimwords (SUC i + p - 1) (:'a) <= dimwords (SUC (i + p)) (:'a)` by
       REWRITE_TAC [DECIDE ``SUC i + p - 1 = i+p``,TWO_dimwords_LE_dinwords_SUC]
  \\ `r < dimwords (SUC (i + p)) (:'a)` by METIS_TAC [LESS_LESS_EQ_TRANS]
  \\ FULL_SIMP_TAC bool_ss [LESS_MOD,ADD]
  \\ REWRITE_TAC [mw_add_mul_spec_simple]
  \\ SIMP_TAC bool_ss [LET_DEF,word_add_n2w,word_mul_n2w]
  \\ Q.SPEC_TAC (`(t * u + r) * q`,`iii`) \\ STRIP_TAC
  \\ REWRITE_TAC [mw_add_mul_spec_simple]    
  \\ REWRITE_TAC [n2mw_def,TL] \\ REWRITE_TAC [GSYM n2mw_def]
  \\ FULL_SIMP_TAC bool_ss [ADD1,ADD_ASSOC,ADD_SUB,w2n_n2w]
  \\ REWRITE_TAC [DECIDE ``r+u*t+n*i:num = i*n+t*u+r``]
  \\ `(iii MOD dimword (:'a) * n + t MOD dimword (:'a) * u + r) DIV
          dimword (:'a) < 2 * dimwords (i + p) (:'a)` by       
    (SIMP_TAC bool_ss [DIV_LT_X,ZERO_LT_dimword,ADD_ASSOC]
     \\ MATCH_MP_TAC BOUNDS \\ ASM_SIMP_TAC bool_ss [GSYM DIVISION,ZERO_LT_dimword])
  \\ Q.PAT_ASSUM `!x.b` (STRIP_ASSUME_TAC o UNDISCH o UNDISCH o UNDISCH o 
       RW [GSYM AND_IMP_INTRO,ADD_ASSOC,ADD_SUB] o
       Q.SPECL [`p+1`,`t DIV dimword (:'a)`,`n`,`q`,
       `(iii MOD dimword (:'a) * n + (t MOD dimword (:'a) * u + r)) DIV dimword (:'a)`])
  \\ ASM_REWRITE_TAC []
  \\ ONCE_REWRITE_TAC [DECIDE ``m+n+k=(m+k)+n:num``]    
  \\ SIMP_TAC bool_ss [GSYM ADD_DIV_ADD_DIV,ZERO_LT_dimword,RIGHT_ADD_DISTRIB,
       DIV_DIV_DIV_MULT,ZERO_LT_dimwords,GSYM (RW1[MULT_COMM]dimwords_SUC),ADD1,
       DIV_MOD_MOD_DIV] 
  \\ REWRITE_TAC [DECIDE ``tt*u*d+m*n*d+(iii*n+t*u+r:num) = tt*d*u+t*u+(m*d*n+iii*n)+r``]
  \\ REWRITE_TAC [GSYM RIGHT_ADD_DISTRIB]
  \\ `t MOD dimword (:'a) = t MOD dimwords (i + 1) (:'a) MOD dimword (:'a)` by 
       SIMP_TAC bool_ss [RW1 [MULT_COMM] dimwords_SUC,GSYM ADD1,
       MOD_MULT_MOD,ZERO_LT_dimwords,ZERO_LT_dimword]
  \\ ASM_SIMP_TAC bool_ss [GSYM DIVISION,ZERO_LT_dimword]
  \\ Q.EXISTS_TAC `m * dimword (:'a) + iii MOD dimword (:'a)`
  \\ REWRITE_TAC [dimwords_SUC,GSYM ADD1]
  \\ STRIP_TAC THEN1 (MATCH_MP_TAC MULT_ADD_LESS_MULT
       \\ ASM_SIMP_TAC bool_ss [GSYM DIVISION,ZERO_LT_dimword,LESS_EQ_REFL])
  \\ REWRITE_TAC [REWRITE_CONV [n2mw_def,HD] ``HD (n2mw (SUC m) n)``]
  \\ ONCE_REWRITE_TAC [n2mw_def] \\ REWRITE_TAC [ADD,CONS_11]
  \\ REWRITE_TAC [RIGHT_ADD_DISTRIB,ADD_ASSOC]  
  \\ ONCE_REWRITE_TAC [DECIDE ``t*u+m*d*n+iii*n+r:num = m*n*d+(t*u+(iii*n+r))``]
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ SIMP_TAC bool_ss [MOD_TIMES,ZERO_LT_dimword]
  \\ ONCE_REWRITE_TAC [DECIDE ``iii*n+r+t*u:num = t*u+(iii*n+r)``]
  \\ SIMP_TAC bool_ss [MOD_MULT_ADD_MOD,ZERO_LT_dimword]);

val mw_monmult1_MULTIPLE = prove(
  ``!i t u n q. 
     t < dimwords i (:'a) /\ u < dimwords i (:'a) /\ n < dimwords i (:'a) ==>
     ?m. m < dimwords i (:'a) /\
       (mw_monmult (n2mw i t) (n2mw (i+2) u) (n2mw (i+2) n) (n2w q) (n2mw (i+1) 0) = 
        n2mw (i+i+1) (t * u + m * n):('a word)list)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC
  ((SIMP_RULE std_ss [LESS_MOD,ZERO_LT_dimwords,AND_IMP_INTRO] o 
    DISCH ``t < dimwords i (:'a)`` o RW [ADD_ASSOC,ADD_0] o
    RW [ZERO_LESS_MULT,ZERO_LT_dimwords,EVAL ``0 < 2``,GSYM ADD_ASSOC,EVAL ``1+1``,ADD_0] o
    RW [ADD_SUB] o Q.SPECL [`i`,`1`,`t`,`n`,`q`,`0`]) mw_monpro1_spec_lemma)
  \\ ASM_REWRITE_TAC []);

val MONTGOMERY_MOD_EQ_0 = prove(
  ``ODD n ==> 0 < n' ==> (n * n' = dimwords i (:'a) * r' - 1) ==> 0 < i ==>
    !k. (k * n' * n + k) MOD dimword (:'a) = 0``,
  ONCE_REWRITE_TAC [DECIDE ``t*n'*n=t*(n*n'):num``]
  \\ Cases_on `i` \\ REWRITE_TAC [EVAL ``0<0:num``]
  \\ SIMP_TAC bool_ss [LEFT_SUB_DISTRIB,MULT_CLAUSES,dimwords_SUC,ADD]  
  \\ REPEAT STRIP_TAC
  \\ `k <= k * (dimwords n'' (:'a) * dimword (:'a) * r')` by ALL_TAC << [
    Cases_on `dimwords n'' (:'a) * dimword (:'a) * r'`
    \\ `0 < n * n'` by ASM_SIMP_TAC bool_ss [ZERO_LESS_MULT,ODD_NON_ZERO] 
    \\ SIMP_TAC bool_ss [MULT_CLAUSES] \\ DECIDE_TAC,
    IMP_RES_TAC SUB_ADD \\ ASM_REWRITE_TAC []
    \\ SIMP_TAC bool_ss [DECIDE ``m*(n''*n*r')=(m*n''*r')*n:num``,MOD_EQ_0,ZERO_LT_dimword]]);

val eq_lemma = 
  (CONJUNCT2 o RW1 [MULT_COMM] o SIMP_RULE std_ss [mod_cmp_def,LET_DEF,
    ZERO_LT_dimword,ZERO_LT_dimwords,LESS_MOD,ZERO_LESS_MULT,ZERO_DIV] o
    Q.INST [`n`|->`0`] o Q.SPECL [`dimword (:'a)`,`dimwords k (:'a)`]) mod_cmp_join;

val mw_monmult1_BOTTOM_ZERO_lemma = prove(
  ``!i l p n n' r' t m r.
     (n * n' = dimwords l (:'a) * r' - 1) ==> ODD n ==> 0 < n' ==> 0 < l ==> 
     (mw_monmult (n2mw i t) (n2mw (i+p+2) u) (n2mw (i+p+2) n) (n2w n') (n2mw (i+p+1) r) = 
       (n2mw (i+i+p+1) m):('a word)list) ==>
     (m MOD dimwords i (:'a) = 0)``,
  Induct THEN1 REWRITE_TAC [dimwords_def,MULT_CLAUSES,EXP,MOD_1]
  \\ REWRITE_TAC [ADD] \\ NTAC 11 STRIP_TAC
  \\ ASM_SIMP_TAC bool_ss [mw_monmult_def,LET_DEF,ADD,n2mw_SUC,HD]
  \\ REWRITE_TAC [GSYM n2mw_SUC,word_add_n2w,word_mul_n2w]
  \\ REWRITE_TAC [GSYM (REWRITE_CONV [n2mw_def] ``n2mw (SUC 0) 0``),n2mw_APPEND]
  \\ SIMP_TAC bool_ss [MULT_CLAUSES,ADD,ADD_0,ZERO_MOD,ZERO_LT_dimwords]
  \\ ASM_REWRITE_TAC [GSYM ADD_ASSOC,EVAL ``1+SUC 0``,mw_add_mul_spec_simple,ADD_0]
  \\ REWRITE_TAC [n2mw_SUC,HD,TL] \\ REWRITE_TAC [GSYM n2mw_SUC,w2n_n2w]
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ REWRITE_TAC [DECIDE ``r+(u*t+n*i):num = i*n+(t*u+r)``]
  \\ SIMP_TAC bool_ss [ZERO_LT_dimword,MOD_MULT_ADD_MOD]
  \\ ONCE_REWRITE_TAC [DECIDE ``m+(n+k)=n+(m+k:num)``]
  \\ SIMP_TAC bool_ss [ZERO_LT_dimword,MOD_MULT_ADD_MOD]
  \\ ONCE_REWRITE_TAC [DECIDE ``m+(n+k)=k+(m+n:num)``]
  \\ SIMP_TAC bool_ss [Once (GSYM MOD_ADD_MOD),ZERO_LT_dimword]
  \\ REWRITE_TAC [RW1 [MULT_COMM] dimwords_SUC]
    \\ SIMP_TAC bool_ss [MOD_MULT_MOD,ZERO_LT_dimword,ZERO_LT_dimwords]
  \\ SIMP_TAC bool_ss [MOD_ADD_MOD,ZERO_LT_dimword]
  \\ ONCE_REWRITE_TAC [DECIDE ``r+(tu+tur)=tur+(tu+r:num)``]
  \\ STRIP_TAC \\ IMP_RES_TAC MONTGOMERY_MOD_EQ_0 \\ ASM_REWRITE_TAC []
  \\ REWRITE_TAC [n2w_mod,GSYM (RW1 [MULT_COMM] dimwords_SUC)]
  \\ REWRITE_TAC [DECIDE ``i+(p+2)=i+(p+1)+1``]  
  \\ FULL_SIMP_TAC bool_ss [DECIDE ``SUC(i+(p+1)+1) = i+(p+1)+2``]
  \\ SIMP_TAC bool_ss [RW1 [MULT_COMM] dimwords_SUC,
        GSYM DIV_DIV_DIV_MULT,ZERO_LT_dimwords,ZERO_LT_dimword]
  \\ REWRITE_TAC [n2mw_SUC,CONS_11]
  \\ ONCE_REWRITE_TAC [DECIDE ``i+(SUC i +(p+1))=i+i+(p+1)+1``]  
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `!m n p. b` IMP_RES_TAC
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ ASM_REWRITE_TAC [eq_lemma]
  \\ FULL_SIMP_TAC bool_ss [n2w_11,LESS_MOD,ZERO_LT_dimword]);

val mw_monmult1_BOTTOM_ZERO = 
  (RW [LESS_EQ_REFL,ADD_0] o Q.SPECL [`i`,`i`,`0`]) mw_monmult1_BOTTOM_ZERO_lemma;

val CALC_MOD = prove(
  ``!m n. 0 < n /\ m < n + n ==> ((if n <= m then m - n else m) = m MOD n:num)``,
  REPEAT STRIP_TAC \\ Cases_on `n <= m` 
  \\ ASM_SIMP_TAC bool_ss [DECIDE ``~(n <= m) ==> m < n:num``,LESS_MOD]
  \\ IMP_RES_TAC LESS_EQUAL_ADD \\ FULL_SIMP_TAC bool_ss [ADD_MODULUS]
  \\ `p < n` by DECIDE_TAC
  \\ ONCE_REWRITE_TAC [ADD_COMM] \\ ASM_SIMP_TAC bool_ss [LESS_MOD,ADD_SUB]);

val mw_monprod_spec = prove(
  ``!t u n n' r' i.
      montprod_vars n n' (dimwords i (:'a)) r' t u ==>
      (mw_monprod (n2mw i t) (n2mw (i+2) u) (n2mw (i+2) n) (n2w n') (n2mw (i+1) 0) =
       n2mw (i+1) ((t * u * r') MOD n) :('a word) list)``,
  REWRITE_TAC [montgomery_vars_def,montprod_vars_def] 
  \\ REPEAT STRIP_TAC \\ SIMP_TAC bool_ss [mw_monprod_def]
  \\ REWRITE_TAC [LENGTH_n2mw,mw_monmult2_EQ_mw_monmult]    
  \\ `t < dimwords i (:'a)` by METIS_TAC [LESS_EQ_LESS_TRANS]
  \\ STRIP_ASSUME_TAC ((UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
       Q.SPECL [`i`,`t`,`u`,`n`,`n'`]) mw_monmult1_MULTIPLE)
  \\ ASM_REWRITE_TAC [] 
  \\ REWRITE_TAC [GSYM ADD_ASSOC,BUTFIRSTN_n2mw] 
  \\ IMP_RES_TAC ODD_NON_ZERO
  \\ `m * n < dimwords i (:'a) * dimwords i (:'a)` by METIS_TAC [MULT_LESS_MULT]
  \\ `n * n < dimwords i (:'a) * dimwords i (:'a)` by METIS_TAC [MULT_LESS_MULT]  
  \\ `t * u < dimwords i (:'a) * dimwords i (:'a)` by METIS_TAC [MULT_LESS_MULT]
  \\ FULL_SIMP_TAC bool_ss [GSYM dimwords_ADD]  
  \\ `t * u + m * n < 2 * dimwords (i+i) (:'a)` by DECIDE_TAC
  \\ `t * u + m * n < dimwords (SUC (i+i)) (:'a)` by 
          METIS_TAC [TWO_dimwords_LE_dinwords_SUC,LESS_LESS_EQ_TRANS]
  \\ `((t * u + m * n) DIV dimwords i (:'a)) < dimwords (SUC (i + i)) (:'a)` by   
       (SIMP_TAC bool_ss [DIV_LT_X,ZERO_LT_dimwords]
        \\ `?k. dimwords i (:'a) = SUC k` 
              by METIS_TAC [NOT_ZERO_LT_ZERO,num_CASES,ZERO_LT_dimwords]
        \\ ASM_SIMP_TAC bool_ss [MULT_CLAUSES,DECIDE ``m < n ==> m < n + n * k:num``])
  \\ ASSUME_TAC (UNDISCH (DECIDE ``n < dimwords i (:'a) ==> n < 2 * dimwords i (:'a)``))
  \\ `!j. n < 2 * dimwords (i + j) (:'a)` by 
       (REWRITE_TAC [dimwords_ADD,MULT_ASSOC] \\ STRIP_TAC
        \\ `?k. dimwords j (:'a) = SUC k` 
              by METIS_TAC [NOT_ZERO_LT_ZERO,num_CASES,ZERO_LT_dimwords]
        \\ ASM_SIMP_TAC bool_ss [MULT_CLAUSES,DECIDE ``m < n ==> m < n + n * k:num``])
  \\ `n < dimwords (SUC (i+i)) (:'a)` by 
          METIS_TAC [TWO_dimwords_LE_dinwords_SUC,LESS_LESS_EQ_TRANS]
  \\ `(t * u + m * n) DIV dimwords i (:'a) < n + n` by 
    (SIMP_TAC bool_ss [DIV_LT_X,ZERO_LT_dimwords,RIGHT_ADD_DISTRIB]
     \\ MATCH_MP_TAC (DECIDE ``m <= n /\ k < l ==> m + k < n + l:num``)
     \\ CONV_TAC ((RAND_CONV o RAND_CONV) (ONCE_REWRITE_CONV [MULT_COMM]))
     \\ ASM_REWRITE_TAC [LT_MULT_RCANCEL]
     \\ MATCH_MP_TAC LESS_EQ_TRANS \\ Q.EXISTS_TAC `n * u`
     \\ ASM_REWRITE_TAC [LE_MULT_LCANCEL,LE_MULT_RCANCEL] \\ DISJ2_TAC
     \\ MATCH_MP_TAC LESS_IMP_LESS_OR_EQ \\ ASM_REWRITE_TAC [])
  \\ SIMP_TAC bool_ss [LET_DEF]
  \\ REWRITE_TAC [mw_sub_spec,GSYM (EVAL ``1+1``),ADD_ASSOC,b2n_def,ADD_0]
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ ONCE_REWRITE_TAC [GSYM n2mw_mod]
  \\ SIMP_TAC bool_ss [LESS_EQ_mw_sub,ZERO_LT_dimwords]
  \\ REWRITE_TAC [n2mw_mod]
  \\ ONCE_REWRITE_TAC [GSYM COND_RAND]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ `(t * u + m * n) DIV dimwords i (:'a) < 2 * dimwords i (:'a)` by DECIDE_TAC
  \\ `((t * u + m * n) DIV dimwords i (:'a) < dimwords (SUC i) (:'a)) /\
      (n < dimwords (SUC i) (:'a))` by   
      (STRIP_TAC \\ MATCH_MP_TAC LESS_LESS_EQ_TRANS
       \\ Q.EXISTS_TAC `2 * dimwords i (:'a)`
       \\ ASM_REWRITE_TAC [TWO_dimwords_LE_dinwords_SUC])
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD,GSYM ADD1]
  \\ ASM_SIMP_TAC bool_ss [CALC_MOD]
  \\ STRIP_ASSUME_TAC (DECIDE ``(i = 0) \/ 0 < i``) << [  
    FULL_SIMP_TAC bool_ss [dimwords_def,MULT_CLAUSES,EXP]
    \\ IMP_RES_TAC (DECIDE ``0 < n /\ n < 1 ==> F``),
    IMP_RES_TAC mw_monmult1_BOTTOM_ZERO
    \\ FULL_SIMP_TAC bool_ss [dimwords_def]
    \\ IMP_RES_TAC MONTGOMERY_LEMMA]);


(* optimisation 1: replacing the inner loops *)

val add_double_mul_def = Define `
  add_double_mul (x:'a word) (y:'a word) (z:'a word) (q:'a word) (c:'a word) (b:'a word) (w:'a word) = 
    let n = w2n w + w2n x * w2n z + w2n y * w2n q + w2n c + w2n b * dimword (:'a) in
      (n2w n,  
       n2w (n DIV dimword (:'a)),
       n2w (n DIV (dimword (:'a) * dimword (:'a)))) : ('a word) # ('a word) # ('a word)`;

val mw_add_mul_mult_def = Define `
  (mw_add_mul_mult [] ys zs p q c b = ([],c,b): (('a word) list) # ('a word) # ('a word)) /\
  (mw_add_mul_mult xs [] zs p q c b = ([],c,b): (('a word) list) # ('a word) # ('a word)) /\
  (mw_add_mul_mult (x::xs) (y::ys) (z::zs) p q c b = 
    let (w,c1,b1) = add_double_mul x y p q c b z in
    let (ws,c2,b2) = mw_add_mul_mult xs ys zs p q c1 b1 in
      (w :: ws,c2,b2))`;

val mw_add_mul_mult_spec = prove(
  ``2 < dimword (:'a) ==>
    !i p q c b n m k.
      mw_add_mul_mult (n2mw i n) (n2mw i m) (n2mw i k) p (q:'a word) (c:'a word) b =
      let sum = k MOD (dimwords i (:'a)) +
                n MOD (dimwords i (:'a)) * w2n p + 
                m MOD (dimwords i (:'a)) * w2n q + 
                w2n c + w2n b * dimword (:'a) 
      in (n2mw i sum, n2w (sum DIV (dimwords i (:'a))), 
          n2w (sum DIV (dimwords (SUC i) (:'a))))``,
  STRIP_TAC \\ Induct << [
    SIMP_TAC bool_ss [n2mw_def,mw_add_mul_mult_def,LET_DEF,dimwords_def,
      MULT_CLAUSES,EXP,MOD_1,ADD_CLAUSES,DIV_1,n2w_w2n]
    \\ REWRITE_TAC [GSYM dimword_def]
    \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ SIMP_TAC bool_ss [DIV_MULT,ZERO_LT_dimword,w2n_lt,MOD_TIMES]
    \\ REWRITE_TAC [n2w_mod,n2w_w2n],
    ASM_REWRITE_TAC [n2mw_def,mw_add_mul_mult_def,add_double_mul_def]
    \\ REWRITE_TAC [GSYM n2mw_SUC]
    \\ SIMP_TAC std_ss [LET_DEF]
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC bool_ss [w2n_n2w]
    \\ `!w:'a word. w2n w < dimword (:'a)` by REWRITE_TAC [w2n_lt]
    \\ `0 < dimword (:'a)` by REWRITE_TAC [ZERO_LT_dimword]
    \\ `0 < dimwords i (:'a)` by REWRITE_TAC [ZERO_LT_dimwords]
    \\ REWRITE_TAC [dimwords_SUC]
    \\ Q.ABBREV_TAC `d = dimword (:'a)`
    \\ Q.ABBREV_TAC `h = dimwords i (:'a)`
    \\ Q.ABBREV_TAC `f = k MOD d + n MOD d * w2n p + m MOD d * w2n q + w2n c + w2n b * d`
    \\ ASM_SIMP_TAC bool_ss [GSYM DIV_DIV_DIV_MULT]
    \\ `(f DIV d DIV d) MOD d = (f DIV d) MOD (d * d) DIV d` by 
          ASM_SIMP_TAC bool_ss [DIV_MOD_MOD_DIV]
    \\ `(f DIV d) MOD d = (f DIV d) MOD (d * d) MOD d` by ASM_SIMP_TAC bool_ss [MOD_MULT_MOD]
    \\ ASM_REWRITE_TAC []
    \\ ONCE_REWRITE_TAC [DECIDE ``m+n+k+l=m+n+(l+k):num``]
    \\ ASM_SIMP_TAC bool_ss [GSYM DIVISION]
    \\ NTAC 2 (Q.PAT_ASSUM `wer = wert:num` (fn x => ALL_TAC)) 
    \\ `f DIV d < d * d` by 
      (Q.UNABBREV_TAC `f` \\ ASM_SIMP_TAC bool_ss [DIV_LT_X]    
      \\ `1 + 1 + 1 <= d` by DECIDE_TAC 
      \\ `?j. d*d*d = d*d*(1+1+1+j)` by METIS_TAC [LESS_EQUAL_ADD]
      \\ ASM_REWRITE_TAC [LEFT_ADD_DISTRIB,MULT_CLAUSES] 
      \\ MATCH_MP_TAC (DECIDE ``m+m'<k /\ n+n'<l /\ j<i ==> m'+m+n+n'+j < k+l+i+p:num``)      
      \\ ASM_SIMP_TAC bool_ss [LT_MULT_RCANCEL] \\ STRIP_TAC
      \\ MATCH_MP_TAC MULT_ADD_LESS_MULT 
      \\ ASM_SIMP_TAC bool_ss [GSYM DIVISION,LESS_IMP_LESS_OR_EQ])
    \\ Q.UNABBREV_TAC `f`
    \\ ASM_SIMP_TAC bool_ss [LESS_MOD,GSYM ADD_DIV_ADD_DIV]
    \\ REWRITE_TAC [RIGHT_ADD_DISTRIB]
    \\ `n MOD d = n MOD (d * h) MOD d` by ASM_SIMP_TAC bool_ss [MOD_MULT_MOD]
    \\ `m MOD d = m MOD (d * h) MOD d` by ASM_SIMP_TAC bool_ss [MOD_MULT_MOD]
    \\ `k MOD d = k MOD (d * h) MOD d` by ASM_SIMP_TAC bool_ss [MOD_MULT_MOD]
    \\ ASM_SIMP_TAC bool_ss [DIV_MOD_MOD_DIV,ADD_ASSOC]
    \\ ONCE_REWRITE_TAC [DECIDE 
          ``km*d+nm*p*d+mm*q*d+k+n*p+m*q+c+b = (km*d+k)+(nm*d*p+n*p)+(mm*d*q+m*q)+c+b:num``]   
    \\ ASM_SIMP_TAC bool_ss [GSYM RIGHT_ADD_DISTRIB,GSYM DIVISION]
    \\ Q.UNABBREV_TAC `d`
    \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ REWRITE_TAC [GSYM ADD_ASSOC]
    \\ ASM_SIMP_TAC bool_ss [MOD_ADD_MOD]
    \\ ONCE_REWRITE_TAC [DECIDE ``m+(n+k)=n+(m+k:num)``]
    \\ ASM_SIMP_TAC bool_ss [MOD_MULT_ADD_MOD]
    \\ ONCE_REWRITE_TAC [DECIDE ``m+(n+(k+q))=k+(m+(n+q):num)``]
    \\ ASM_SIMP_TAC bool_ss [MOD_MULT_ADD_MOD]
    \\ REWRITE_TAC [n2w_mod,n2mw_SUC]
    \\ ASM_SIMP_TAC bool_ss [AC MULT_COMM MULT_ASSOC,AC ADD_COMM ADD_ASSOC,
         DIV_DIV_DIV_MULT,ZERO_LESS_MULT]]);

val FST_mw_add_mul_mult = prove(
  ``2 < dimword (:'a) ==>
    (FST (mw_add_mul_mult (n2mw i n) (n2mw i m) (n2mw i k) p q 0w 0w) =
     n2mw i (k + n * w2n p + m * w2n q): ('a word) list)``,
  SIMP_TAC bool_ss [mw_add_mul_mult_spec,LET_DEF,FST,w2n_n2w,
    ZERO_LT_dimword,LESS_MOD,MULT_CLAUSES,ADD_0] 
  \\ REWRITE_TAC [GSYM ADD_ASSOC]
  \\ ONCE_REWRITE_TAC [GSYM n2mw_mod]
  \\ SIMP_TAC bool_ss [ZERO_LT_dimwords,MOD_ADD_MOD]
  \\ ONCE_REWRITE_TAC [DECIDE ``m+(n+k)=n+(k+m:num)``]
  \\ ASM_SIMP_TAC bool_ss [ZERO_LT_dimwords,MOD_MULT_ADD_MOD]
  \\ ONCE_REWRITE_TAC [DECIDE ``m+(n+k)=n+(k+m:num)``]
  \\ ASM_SIMP_TAC bool_ss [ZERO_LT_dimwords,MOD_MULT_ADD_MOD]);

val mw_add_mul_EQ_mw_add_mul_mult = prove(
  ``2 < dimword (:'a) ==> 
    !x y i k m n.
      mw_add_mul y (n2mw i n) (mw_add_mul x (n2mw i m) (n2mw i k)) =
      FST (mw_add_mul_mult (n2mw i m) (n2mw i n) (n2mw i k) x y 0w (0w:'a word))``,
  STRIP_TAC \\ Cases_word \\ Cases_word \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC bool_ss [FST_mw_add_mul_mult,mw_add_mul_spec_simple]
  \\ SIMP_TAC bool_ss [w2n_n2w,AC ADD_COMM ADD_ASSOC,AC MULT_COMM MULT_ASSOC]);

val smart_add_mul_mult_def = Define `
  smart_add_mul_mult xs ys zs p q c1 b1 =
    let (ws,c2,b2) = mw_add_mul_mult xs ys zs p q c1 b1 in 
    let (w3,c3,b3) = add_double_mul 0w 0w p q c2 b2 (LAST zs) in
    let (w4,c4,b4) = add_double_mul 0w 0w p q c3 b3 0w in
      ws ++ [w3;w4]`;

val smart_add_mul_mult2_def = Define `
  smart_add_mul_mult2 (x::xs) (y::ys) (z::zs) p q =
     let (w1,c1,b1) = add_double_mul x y p q 0w 0w z in
     let (ws,c2,b2) = mw_add_mul_mult xs ys zs p q c1 b1 in
     let (w3,c3,b3) = add_double_mul 0w 0w p q c2 b2 (LAST zs) in
     let (w4,c4,b4) = add_double_mul 0w 0w p q c3 b3 0w in
       ws ++ [w3; w4]`;

val push_FST_into_LET = prove(
  ``FST (let (w,c1,b1) = g in let (ws,c2,b2) = f c1 b1 in (w::ws,c2,b2)) =
    let (w,c1,b1) = g in w :: FST (f c1 b1)``,
  Cases_on `g` \\ Cases_on `r` \\ SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `f q' r'` \\ Cases_on `r` \\ SIMP_TAC std_ss [LET_DEF]);

val smart_add_mult_lemma = prove(
  ``!i m n k x y c b.
      FST (mw_add_mul_mult (n2mw i m ++ [0w;0w]) (n2mw i n ++ [0w;0w]) (n2mw (i+1) k ++ [0w]) x y c (b:'a word)) =
      smart_add_mul_mult (n2mw i m) (n2mw i n) (n2mw (i+1) k) x y c b``,
  Induct << [
    SIMP_TAC bool_ss [n2mw_def,APPEND,GSYM (EVAL ``SUC 0``),ADD]
    \\ REWRITE_TAC [mw_add_mul_mult_def,smart_add_mul_mult_def,LAST_DEF]
    \\ SIMP_TAC std_ss [LET_DEF,APPEND,add_double_mul_def],
    REWRITE_TAC [ADD,n2mw_def,mw_add_mul_mult_def,APPEND]
    \\ ASM_REWRITE_TAC [push_FST_into_LET]
    \\ `!x i n. LAST (x::n2mw (i+1) n) = LAST (n2mw (i+1) n)` by
          REWRITE_TAC [n2mw_def,LAST_DEF,NOT_CONS_NIL,GSYM ADD1]
    \\ ASM_REWRITE_TAC [smart_add_mul_mult_def,mw_add_mul_mult_def]
    \\ REPEAT STRIP_TAC
    \\ Q.SPEC_TAC (`add_double_mul (n2w m) (n2w n) x y c b (n2w k)`,`iii`)
    \\ Cases \\ Cases_on `r`
    \\ SIMP_TAC std_ss [LET_DEF]
    \\ Q.PAT_ABBREV_TAC `nnn = mw_add_mul_mult mm nn kk x y q' r'`
    \\ Cases_on `nnn` \\ Cases_on `r`
    \\ SIMP_TAC std_ss [LET_DEF,add_double_mul_def,APPEND]]);

val mw_monmult4_step_def = Define `
  mw_monmult4_step (y::ys) (n::ns) (z::zs) x m = 
    let u = (x * y + z) * m in
      smart_add_mul_mult2 (y::ys) (n::ns) (z::zs) x u`;

val mw_monmult4_def = Define `
  (mw_monmult4 [] ys ns m zs = zs) /\
  (mw_monmult4 (x::xs) (y::ys) (n::ns) m (z::zs) =  
    let ws = mw_monmult4_step (y::ys) (n::ns) (z::zs) x m in
      mw_monmult4 xs (y::ys) (n::ns) m ws)`;

val mw_monprod4_def = Define `
  mw_monprod4 xs ys ns m zs = 
    let zs = mw_monmult4 xs ys ns m zs in
    let (zs',c) = mw_sub zs (ns ++ [0w;0w]) T in
      (if c then zs' else zs)`;

val n2mw_ADD_2 = prove(
  ``!n i. n2mw i n ++ [0w;0w:'a word] = n2mw (i+2) (n MOD dimwords i (:'a))``,
  REWRITE_TAC [GSYM (SIMP_CONV bool_ss 
       [n2mw_def,LESS_DIV_EQ_ZERO,ZERO_LT_dimword] ``n2mw (SUC (SUC 0)) 0``)]
  \\ SIMP_TAC bool_ss [EVAL ``SUC (SUC 0)``,n2mw_APPEND,MULT_CLAUSES,ADD_0]);

val n2mw_ADD_1 = prove(
  ``!n i. n2mw (i+1) n ++ [0w:'a word] = n2mw (i+2) (n MOD dimwords (i+1) (:'a))``,
  REWRITE_TAC [GSYM (REWRITE_CONV [n2mw_def] ``n2mw (SUC 0) 0``)]
  \\ SIMP_TAC bool_ss [EVAL ``SUC 0``,n2mw_APPEND,MULT_CLAUSES,ADD_0]
  \\ REWRITE_TAC [EVAL ``1+1``,GSYM ADD_ASSOC]);

val lemma = prove(
  ``2 < dimword (:'a) ==> n < dimwords i (:'a) /\ m < dimwords i (:'a) ==>
    (mw_add_mul y (n2mw i n ++ [0w;0w]) (mw_add_mul x (n2mw i m ++ [0w;0w]) (n2mw (i+1) k ++ [0w])) =
     smart_add_mul_mult (n2mw i m) (n2mw i n) (n2mw (i+1) k) x y 0w (0w:'a word))``,  
  REWRITE_TAC [GSYM smart_add_mult_lemma,n2mw_ADD_2,n2mw_ADD_1]    
  \\ SIMP_TAC bool_ss [mw_add_mul_EQ_mw_add_mul_mult,LESS_MOD]);

val n2mw_EXISTS = prove(
  ``!xs:('a word) list. ?k. (xs = n2mw (LENGTH xs) k) /\ k < dimwords (LENGTH xs) (:'a)``,
  Induct \\ REWRITE_TAC [n2mw_def,LENGTH]
  THEN1 (Q.EXISTS_TAC `0` \\ REWRITE_TAC [dimwords_def,EXP,MULT_CLAUSES] \\ EVAL_TAC)
  \\ POP_ASSUM (STRIP_ASSUME_TAC o GSYM) \\ REPEAT STRIP_TAC   
  \\ Q.EXISTS_TAC `k * dimword (:'a) + w2n h`  
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ ASM_SIMP_TAC bool_ss [DIV_MULT,w2n_lt,MOD_MULT,n2w_w2n,dimwords_SUC]
  \\ MATCH_MP_TAC MULT_ADD_LESS_MULT \\ ASM_REWRITE_TAC [w2n_lt,LESS_EQ_REFL]);

val mw_add_mul_EQ_smart_add_mul_mult = prove(
  ``2 < dimword (:'a) ==> 
    (LENGTH xs = LENGTH ys) /\ (LENGTH zs = SUC (LENGTH ys)) ==>
    (mw_add_mul y (ys ++ [0w;0w]) (mw_add_mul x (xs ++ [0w;0w]) (zs ++ [0w])) =
     smart_add_mul_mult xs ys zs x y 0w (0w:'a word))``,  
  REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `i = LENGTH ys`
  \\ `?m. (xs = n2mw i m) /\ m < dimwords i (:'a)` by METIS_TAC [n2mw_EXISTS]
  \\ `?n. (ys = n2mw i n) /\ n < dimwords i (:'a)` by METIS_TAC [n2mw_EXISTS]
  \\ `?k. (zs = n2mw (SUC i) k) /\ k < dimwords (SUC i) (:'a)` by METIS_TAC [n2mw_EXISTS]
  \\ ASM_SIMP_TAC bool_ss [GSYM smart_add_mult_lemma,n2mw_ADD_2,n2mw_ADD_1,LESS_MOD,ADD1]    
  \\ ASM_SIMP_TAC bool_ss [mw_add_mul_EQ_mw_add_mul_mult,LESS_MOD])

val TL_smart_add_mul_mult = prove(
  ``~(zs = []) ==>
    (TL (smart_add_mul_mult (x::xs) (y::ys) (z::zs) p q 0w 0w) =
     smart_add_mul_mult2 (x::xs) (y::ys) (z::zs) p q)``,
  REWRITE_TAC [smart_add_mul_mult_def,smart_add_mul_mult2_def,mw_add_mul_mult_def]
  \\ Q.SPEC_TAC (`add_double_mul x y p q 0w 0w z`,`ddd`)
  \\ Cases \\ Cases_on `r` \\ SIMP_TAC std_ss [LET_DEF]
  \\ Q.SPEC_TAC (`mw_add_mul_mult xs ys zs p q q'' r'`,`ddd`)
  \\ Cases \\ Cases_on `r` \\ SIMP_TAC std_ss [LAST_DEF]
  \\ Q.SPEC_TAC (`add_double_mul 0w 0w p q q''' r' (LAST zs)`,`ddd`)
  \\ Cases \\ Cases_on `r` \\ SIMP_TAC std_ss []
  \\ Q.SPEC_TAC (`add_double_mul 0w 0w p q q'''' r' 0w`,`ddd`)
  \\ Cases \\ Cases_on `r` \\ SIMP_TAC std_ss [TL,APPEND]);

val LENGTH_IMP_LENGTH_TL = prove(
  ``!xs n. (LENGTH xs = SUC n) ==> (LENGTH (TL xs) = n)``,
  Cases \\ REWRITE_TAC [LENGTH] THEN1 DECIDE_TAC
  \\ REWRITE_TAC [ADD1,EQ_ADD_RCANCEL,TL]);

val EXPAND_add_mul = prove(    
  ``(let (z',c1) = g in
     let (zs,c2) = h z c1 in (z'::zs,c2)) =
    ((FST g)::(FST (h z (SND g))), (SND (h z (SND g))))``,
  SIMP_TAC bool_ss [LET_DEF] 
  \\ Cases_on `g` \\ SIMP_TAC std_ss [] \\ Cases_on `(h z r)` \\ SIMP_TAC std_ss []);
 
val LENGTH_FST_mw_add = prove(
  ``!xs ys c. LENGTH xs <= LENGTH ys ==> (LENGTH (FST (mw_add xs ys c)) = LENGTH xs)``,
  Induct \\ REPEAT STRIP_TAC \\ Cases_on `ys` 
  \\ REWRITE_TAC [mw_add_def,EXPAND_add_mul,LENGTH,ADD1,EQ_ADD_RCANCEL]
  \\ FULL_SIMP_TAC bool_ss [LENGTH,DECIDE ``n + 1 <= 0 = F``,ADD1,LE_ADD_RCANCEL]);

val LENGTH_FST_mw_mul = prove(
  ``!xs y c. LENGTH (FST (mw_mul xs y c)) = LENGTH xs``,
  Induct \\ ASM_REWRITE_TAC [mw_mul_def,EXPAND_add_mul,LENGTH]);

val LENGTH_add_mul = prove(
  ``!h ys zs. LENGTH zs <= LENGTH ys ==> (LENGTH (mw_add_mul h ys zs) = LENGTH zs)``,
  REWRITE_TAC [mw_add_mul_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC LENGTH_FST_mw_add \\ ASM_REWRITE_TAC [LENGTH_FST_mw_mul]);

val mw_monmult2_EQ_mw_monmult4 = prove(
  ``2 < dimword (:'a) ==> 
    !xs y ys n ns z zs m.
      (LENGTH (z::zs) = SUC (LENGTH (n::ns))) /\ (LENGTH (y::ys) = LENGTH (n::ns)) ==>
      (mw_monmult2 xs (y::ys ++ [0w;0w]) (n::ns ++ [0w;0w]) m (z::zs) = 
       mw_monmult4 xs (y::ys) (n::ns) m (z:'a word ::zs))``,
  STRIP_TAC \\ Induct \\ REWRITE_TAC [mw_monmult4_def,mw_monmult2_def] 
  \\ REPEAT STRIP_TAC
  \\ CONV_TAC ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss [LET_DEF]))
  \\ Q.PAT_ABBREV_TAC `uuu = TL (mw_add_mul mmmm nnn zzzz)`
  \\ `LENGTH uuu = LENGTH (z::zs)` by ALL_TAC << [
    Q.UNABBREV_TAC `uuu`
    \\ MATCH_MP_TAC LENGTH_IMP_LENGTH_TL
    \\ `LENGTH (y::ys ++ [0w; 0w]) = LENGTH (z::zs ++ [0w])` by 
          ASM_REWRITE_TAC [LENGTH_APPEND,LENGTH,ADD_CLAUSES] 
    \\ `LENGTH (n::ns ++ [0w; 0w]) = LENGTH (z::zs ++ [0w])` by 
          ASM_REWRITE_TAC [LENGTH_APPEND,LENGTH,ADD_CLAUSES]  
    \\ `LENGTH (z::zs ++ [0w]) = LENGTH (mw_add_mul h (y::ys ++ [0w; 0w]) (z::zs ++ [0w]))` 
       by (MATCH_MP_TAC (GSYM LENGTH_add_mul) \\ ASM_REWRITE_TAC [LESS_EQ_REFL])
    \\ Q.PAT_ASSUM `LENGTH zs = SUC (LENGTH ys)` (ASSUME_TAC o GSYM)
    \\ `SUC (LENGTH (z::zs)) = LENGTH (z::zs ++ [0w])` by 
        REWRITE_TAC [LENGTH_APPEND,LENGTH,ADD_CLAUSES]    
    \\ ASM_REWRITE_TAC []
    \\ MATCH_MP_TAC LENGTH_add_mul
    \\ ASM_REWRITE_TAC [LESS_EQ_REFL],
    Q.UNDISCH_TAC `LENGTH uuu = LENGTH (z::zs)`
    \\ Q.UNABBREV_TAC `uuu`
    \\ ASM_SIMP_TAC bool_ss [mw_add_mul_EQ_smart_add_mul_mult,mw_monmult4_step_def,LET_DEF]
    \\ Cases_on `zs = []`
    THEN1 (FULL_SIMP_TAC bool_ss [LENGTH] \\ `F` by DECIDE_TAC)
    \\ ASM_SIMP_TAC bool_ss [APPEND,HD,TL_smart_add_mul_mult]
    \\ SIMP_TAC bool_ss [LET_DEF]
    \\ REWRITE_TAC [CONJUNCT2 (GSYM APPEND)] 
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_ABBREV_TAC `ddd = smart_add_mul_mult2 yys nns zzs hh hhh`
    \\ Cases_on `ddd` THEN1 (FULL_SIMP_TAC bool_ss [LENGTH] \\ `F` by DECIDE_TAC)  
    \\ Q.PAT_ASSUM `!ys.b` MATCH_MP_TAC
    \\ ASM_REWRITE_TAC []]);
              
val mw_monprod4_EQ_monprod = prove(
  ``2 < dimword (:'a) ==> 
    !xs ys ns zs m:'a word. 
      (LENGTH zs = SUC (LENGTH ns)) /\ (LENGTH xs = LENGTH ys) /\ (LENGTH ys = LENGTH ns) ==>
      (mw_monprod4 xs ys ns m zs = mw_monprod xs (ys++[0w;0w]) (ns++[0w;0w]) m zs)``,
  STRIP_TAC \\ Cases \\ REWRITE_TAC [mw_monprod4_def,mw_monprod_def]
  THEN1 SIMP_TAC bool_ss [mw_monmult4_def,mw_monmult2_def]
  \\ NTAC 3 (Cases THEN1 SIMP_TAC bool_ss [LENGTH,DECIDE ``~(SUC n = 0)``])
  \\ ASM_SIMP_TAC bool_ss [mw_monmult2_EQ_mw_monmult4]);
  
val mw_monprod4_spec = prove(
  ``2 < dimword (:'a) ==> 
    !t u n n' r' i.
      montprod_vars n n' (dimwords i (:'a)) r' t u ==>
      (mw_monprod4 (n2mw i t) (n2mw i u) (n2mw i n) (n2w n') (n2mw (i+1) 0) =
       n2mw (i+1) ((t * u * r') MOD n) :('a word) list)``,
  REPEAT STRIP_TAC
  \\ `t < dimwords i (:'a) /\ u < dimwords i (:'a) /\ n < dimwords i (:'a)` by 
       (FULL_SIMP_TAC bool_ss [montgomery_vars_def,montprod_vars_def] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC bool_ss [mw_monprod4_EQ_monprod,LENGTH_n2mw,ADD1]
  \\ ASM_SIMP_TAC bool_ss [n2mw_ADD_2,LESS_MOD,mw_monprod_spec]);


(* optimisation 2: reduce the size of zs *)

val mw_monmult5_step_def = Define `
  mw_monmult5_step (x::xs) (y::ys) (z::zs) z' p m =
     let q = (p * x + z) * m in
     let (w1,c1,b1) = add_double_mul x y p q 0w 0w z in
     let (ws,c2,b2) = mw_add_mul_mult xs ys zs p q c1 b1 in
     let (w3,c3,b3) = add_double_mul 0w 0w p q c2 b2 z' in
     let (w4,c4,b4) = add_double_mul 0w 0w p q c3 b3 0w in
       (ws ++ [w3],w4)`;

val mw_monmult5_def = Define `
  (mw_monmult5 [] ys ns m zs q = (zs,q)) /\
  (mw_monmult5 (x::xs) (y::ys) (n::ns) m (z::zs) q =  
    let (ws,w) = mw_monmult5_step (y::ys) (n::ns) (z::zs) q x m in
      mw_monmult5 xs (y::ys) (n::ns) m ws w)`;

val mw_monprod5_def = Define `
  mw_monprod5 xs ys ns m zs z = 
    let (zs,z) = mw_monmult5 xs ys ns m zs z in
    let (zs',c) = mw_sub zs ns T in
    let c' = SND (single_sub z 0w c) in
      (if c' then zs' else zs)`;

fun RENAME_TAC [] = ALL_TAC
  | RENAME_TAC ((x,y)::xs) = Q.SPEC_TAC (x,y) \\ STRIP_TAC \\ RENAME_TAC xs;

val mw_add_mul_mult_cases = cases_thm "mw_add_mul_mult_cases" [mw_add_mul_mult_def]
    [``FST (mw_add_mul_mult [] [] zs p q c b)``,
     ``SND (mw_add_mul_mult [] [] zs p q c b)``,
     ``FST (mw_add_mul_mult (x::xs) (y::ys) (z::zs) p q c b)``,
     ``SND (mw_add_mul_mult (x::xs) (y::ys) (z::zs) p q c b)``]

val LENGTH_FST_mw_add_mul_mult = store_thm("LENGTH_FST_mw_add_mul_mult",
  ``!xs ys zs p q b c.
      (LENGTH xs = LENGTH ys) /\ (LENGTH ys = LENGTH zs) ==>
      (LENGTH (FST (mw_add_mul_mult (xs:('a word) list) ys zs p q b c)) = LENGTH xs)``,
  Induct \\ Cases_on `ys` \\ Cases_on `zs` \\ REWRITE_TAC [LENGTH,ADD1,mw_add_mul_mult_cases] 
  \\ REPEAT DECIDE_TAC \\ ASM_SIMP_TAC bool_ss [EQ_ADD_RCANCEL] \\ METIS_TAC []);

val LENGTH_FST_mw_monmult5_step = store_thm("LENGTH_FST_mw_monmult5_step",
  ``(LENGTH xs = LENGTH ys) /\ (LENGTH ys = LENGTH zs) ==>
    (LENGTH (FST (mw_monmult5_step (x::xs) (y::ys) (z::zs) z' p m)) = LENGTH (x::xs))``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [mw_monmult5_step_def,LET_DEF]
  \\ Cases_on `add_double_mul x y p ((p * x + z) * m) 0w 0w z`
  \\ Cases_on `r` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `mw_add_mul_mult xs ys zs p ((p * x + z) * m) q' r'`
  \\ Cases_on `r` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `add_double_mul 0w 0w p ((p * x + z) * m) q''' r'' z'`
  \\ Cases_on `r` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `add_double_mul 0w 0w p ((p * x + z) * m) q''''' r''' 0w`
  \\ Cases_on `r` \\ ASM_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,ADD1]
  \\ `q'' = FST (mw_add_mul_mult xs ys zs p ((p * x + z) * m) q' r')` by 
        METIS_TAC [PAIR_EQ,PAIR]
  \\ METIS_TAC [LENGTH_FST_mw_add_mul_mult]);

val LENGTH_FST_mw_monmult5 = store_thm("LENGTH_FST_mw_monmult5",
  ``!us xs ys zs q m.
      ~(LENGTH xs = 0) /\ (LENGTH ys = LENGTH xs) /\ (LENGTH zs = LENGTH ys) ==>
      (LENGTH (FST (mw_monmult5 us xs ys m zs q)) = LENGTH xs)``,
  Induct \\ SIMP_TAC bool_ss [mw_monmult5_def] 
  \\ Cases_on `xs` \\ Cases_on `ys` \\ Cases_on `zs`
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,EQ_ADD_RCANCEL,mw_monmult5_def,LET_DEF] 
  \\ REPEAT STRIP_TAC \\ REPEAT DECIDE_TAC
  \\ ASM_REWRITE_TAC [GSYM (REWRITE_CONV [LENGTH,ADD1] ``LENGTH (h::t)``)]
  \\ Cases_on `mw_monmult5_step (h::t) (h'::t') (h''::t'') q h''' m`
  \\ SIMP_TAC std_ss [] \\ Q.PAT_ASSUM `!xs.b` MATCH_MP_TAC
  \\ ASM_REWRITE_TAC [LENGTH,ADD1,EQ_ADD_RCANCEL] 
  \\ REPEAT STRIP_TAC \\ REPEAT DECIDE_TAC
  \\ ASM_REWRITE_TAC [GSYM (REWRITE_CONV [LENGTH,ADD1] ``LENGTH (h::t)``)]
  \\ `q' = FST (mw_monmult5_step (h::t) (h'::t') (h''::t'') q h''' m)` by METIS_TAC [FST] 
  \\ ONCE_ASM_REWRITE_TAC []
  \\ MATCH_MP_TAC LENGTH_FST_mw_monmult5_step \\ ASM_REWRITE_TAC []);

val mw_add_mul_mult_SNOC = prove(
  ``!xs ys zs z p q c b.
      (LENGTH xs = LENGTH ys) /\ (LENGTH ys = LENGTH zs) ==>
      (mw_add_mul_mult xs ys (SNOC z zs) p q c b = mw_add_mul_mult xs ys zs p q c b)``,
  Induct \\ REWRITE_TAC [SNOC_APPEND]
  THEN1 (Cases \\ REWRITE_TAC [mw_add_mul_mult_def,LENGTH,DECIDE ``~(0 = SUC n)``])
  \\ STRIP_TAC \\ NTAC 2 (Cases \\ REWRITE_TAC [LENGTH,DECIDE ``~(SUC n = 0)``])
  \\ RENAME_TAC [(`h`,`x`),(`h'`,`y`),(`h''`,`z`),(`t`,`ys`),(`t'`,`zs`)]
  \\ REWRITE_TAC [APPEND,mw_add_mul_mult_def,DECIDE ``(SUC n = SUC m) = (n = m)``]  
  \\ REWRITE_TAC [GSYM SNOC_APPEND] \\ REPEAT STRIP_TAC
  \\ Q.SPEC_TAC (`add_double_mul x y p q c b z`,`ddd`) \\ Cases \\ Cases_on `r`
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ Q.PAT_ASSUM `!ys.b` MATCH_MP_TAC \\ ASM_REWRITE_TAC []);

val mw_monmult_step_4_EQ_5 = prove(
  ``(LENGTH xs = LENGTH ys) /\ (LENGTH ys = LENGTH zs) ==>
    (mw_monmult4_step (x::xs) (y::ys) (SNOC u (z::zs)) p q =
     let (ts,t) = mw_monmult5_step (x::xs) (y::ys) (z::zs) u p q in SNOC t ts)``,
  REWRITE_TAC [SNOC_APPEND,APPEND,mw_monmult4_step_def,smart_add_mul_mult2_def]  
  \\ REWRITE_TAC [mw_monmult5_step_def]
  \\ SIMP_TAC bool_ss [GSYM SNOC_APPEND,LAST,mw_add_mul_mult_SNOC,mw_monmult4_step_def]
  \\ Q.SPEC_TAC (`(p * x + z) * q`,`qq`) \\ STRIP_TAC \\ SIMP_TAC std_ss [LET_DEF]
  \\ Q.SPEC_TAC (`add_double_mul x y p qq 0w 0w z`,`ddd`)
  \\ Cases \\ Cases_on `r` \\ SIMP_TAC std_ss [LET_DEF]
  \\ Q.SPEC_TAC (`mw_add_mul_mult xs ys zs p qq q' r'`,`ddd`)
  \\ Cases \\ Cases_on `r` \\ SIMP_TAC std_ss [LET_DEF]
  \\ Q.SPEC_TAC (`add_double_mul 0w 0w p qq q' r' u`,`ddd`)
  \\ Cases \\ Cases_on `r` \\ SIMP_TAC std_ss [LET_DEF]
  \\ Q.SPEC_TAC (`add_double_mul 0w 0w p qq q'' r' 0w`,`ddd`)
  \\ Cases \\ Cases_on `r` \\ SIMP_TAC std_ss [LET_DEF]
  \\ REWRITE_TAC [GSYM APPEND_ASSOC,APPEND,SNOC_APPEND]);

val LENGTH_mw_add_mul_mult = prove(
  ``!xs ys zs p q c b.
      (LENGTH xs = LENGTH ys) /\ (LENGTH ys <= LENGTH zs) ==>
      (LENGTH (FST (mw_add_mul_mult xs ys zs p q c b)) = LENGTH xs)``,
  Induct  
  THEN1 (Cases \\ REWRITE_TAC [mw_add_mul_mult_def,LENGTH,DECIDE ``~(0 = SUC n)``])
  \\ STRIP_TAC \\ Cases \\ REWRITE_TAC [LENGTH,DECIDE ``~(SUC n = 0)``]
  \\ Cases \\ REWRITE_TAC [LENGTH,DECIDE ``~(n + 1 <= 0)``,ADD1,EQ_ADD_RCANCEL,LE_ADD_RCANCEL]
  \\ REWRITE_TAC [mw_add_mul_mult_def] \\ REPEAT STRIP_TAC
  \\ Q.SPEC_TAC (`add_double_mul h h' p q c b h''`,`ddd`)
  \\ Cases \\ Cases_on `r` \\ SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `mw_add_mul_mult xs t t' p q q'' r'` \\ Cases_on `r`
  \\ SIMP_TAC std_ss [LENGTH,ADD1]
  \\ `q''' = FST (mw_add_mul_mult xs t t' p q q'' r')` by ALL_TAC
  \\ FULL_SIMP_TAC bool_ss [FST]);

val LENGTH_mw_monmult5_step = prove(
  ``(LENGTH ys = LENGTH ns) /\ (LENGTH ns = LENGTH zs) ==> 
    ((LENGTH (FST (mw_monmult5_step (y::ys) (n::ns) (z::zs) q x u))) = SUC (LENGTH zs))``,
  REWRITE_TAC [mw_monmult5_step_def]
  \\ Q.SPEC_TAC (`(x * y + z) * u`,`t`) \\ STRIP_TAC \\ SIMP_TAC std_ss [LET_DEF] 
  \\ Q.SPEC_TAC (`add_double_mul y n x t 0w 0w z`,`ddd`)
  \\ Cases \\ Cases_on `r` \\ SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `mw_add_mul_mult ys ns zs x t q'' r'` \\ Cases_on `r` 
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `add_double_mul 0w 0w x t q''' r'' q` \\ Cases_on `r`
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `add_double_mul 0w 0w x t q''''' r''' 0w` \\ Cases_on `r`
  \\ SIMP_TAC std_ss [LET_DEF,LENGTH_APPEND,LENGTH,ADD_CLAUSES,ADD1]
  \\ `q' = FST (mw_add_mul_mult ys ns zs x t q'' r')` by ALL_TAC
  \\ FULL_SIMP_TAC bool_ss [FST,LENGTH_mw_add_mul_mult,LESS_EQ_REFL]);

val LENGTH_mw_monmult5 = prove(
  ``!xs ys ns zs m q.
      (LENGTH xs <= LENGTH ys) /\ (LENGTH ys = LENGTH ns) /\ (LENGTH ns = LENGTH zs) ==>
      (LENGTH (FST (mw_monmult5 xs ys ns m zs q)) = LENGTH zs)``,
  Induct \\ REWRITE_TAC [mw_monmult5_def] \\ STRIP_TAC
  \\ NTAC 3 (Cases \\ REWRITE_TAC [LENGTH,DECIDE ``~(SUC n <= 0)``,DECIDE ``~(SUC n = 0)``])
  \\ SIMP_TAC std_ss [mw_monmult5_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `mw_monmult5_step (h'::t) (h''::t') (h'''::t'') q h m`
  \\ SIMP_TAC std_ss []
  \\ `SUC (LENGTH t'') = LENGTH q'` by ALL_TAC << [ 
    `q' = FST (mw_monmult5_step (h'::t) (h''::t') (h'''::t'') q h m)` by ALL_TAC
    \\ FULL_SIMP_TAC bool_ss [FST,LENGTH_mw_add_mul_mult,LESS_EQ_REFL]
    \\ MATCH_MP_TAC (GSYM LENGTH_mw_monmult5_step) \\ ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [] \\ Q.PAT_ASSUM `!ys.b` MATCH_MP_TAC
    \\ ASM_REWRITE_TAC [LENGTH] \\ DECIDE_TAC]);

val mw_monmult4_EQ_mw_monmult5 = prove(
  ``!xs ys ns zs m q.
      (LENGTH xs <= LENGTH ys) /\ (LENGTH ys = LENGTH ns) /\ (LENGTH ns = LENGTH zs) ==>
      (mw_monmult4 xs ys ns m (zs ++ [q]) = 
       let (zs,q) = mw_monmult5 xs ys ns m zs q in zs ++ [q])``,
  Induct THEN1 SIMP_TAC std_ss [mw_monmult4_def,mw_monmult5_def,LET_DEF] \\ STRIP_TAC
  \\ NTAC 3 (Cases THEN1 SIMP_TAC bool_ss [LENGTH,DECIDE ``~(SUC n <= 0) /\ ~(SUC n = 0)``])
  \\ RENAME_TAC [(`h`,`x`),(`h'`,`y`),(`h''`,`n`),(`h'''`,`z`)]
  \\ RENAME_TAC [(`t`,`ys`),(`t'`,`ns`),(`t''`,`zs`)]
  \\ REWRITE_TAC [mw_monmult4_def,APPEND,mw_monmult5_def]
  \\ REWRITE_TAC [SNOC_APPEND,LAST,LENGTH,ADD1,EQ_ADD_RCANCEL,GSYM (CONJUNCT2 APPEND)]
  \\ SIMP_TAC bool_ss [GSYM SNOC_APPEND,mw_monmult_step_4_EQ_5]
  \\ SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `mw_monmult5_step (y::ys) (n::ns) (z::zs) q x m` 
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,LET_DEF]
  \\ Q.PAT_ASSUM `!ys.b` MATCH_MP_TAC
  \\ ASM_SIMP_TAC bool_ss [LENGTH,DECIDE ``m<=n ==> m <= SUC n``]
  \\ `q' = FST (mw_monmult5_step (y::ys) (n::ns) (z::zs) q x m)` by ALL_TAC
  \\ FULL_SIMP_TAC bool_ss [FST,GSYM LENGTH_mw_monmult5_step]);

val mw_sub_APPEND = prove(
  ``!xs zs ys qs b. 
     (LENGTH xs = LENGTH zs) ==> 
     (mw_sub (xs++ys) (zs++qs) b = 
      let (rs,c) = mw_sub xs zs b in let (rs',c') = mw_sub ys qs c in (rs++rs',c'))``,
  Induct << [
    Cases \\ FULL_SIMP_TAC std_ss [mw_sub_def,LET_DEF,APPEND,LENGTH,DECIDE ``~(0 = SUC n)``]
    \\ Cases_on `mw_sub ys qs b` \\ SIMP_TAC std_ss [],
    STRIP_TAC \\ Cases \\ REWRITE_TAC [LENGTH,DECIDE ``~(SUC n = 0)``]
    \\ ASM_SIMP_TAC bool_ss [ADD1,EQ_ADD_RCANCEL,APPEND,mw_sub_def]  
    \\ REPEAT STRIP_TAC
    \\ Q.SPEC_TAC (`single_sub h h' b`,`ddd`) \\ Cases \\ SIMP_TAC std_ss [LET_DEF]
    \\ Q.SPEC_TAC (`mw_sub xs t r`,`ddd`) \\ Cases \\ SIMP_TAC std_ss [LET_DEF]
    \\ Q.SPEC_TAC (`mw_sub ys qs r`,`ddd`) \\ Cases \\ SIMP_TAC std_ss [LET_DEF]
    \\ REWRITE_TAC [APPEND]]);

val mw_monprod_5_EQ_4 = prove( 
  ``!xs ys ns zs m q.
      (LENGTH xs = LENGTH ys) /\ (LENGTH ys = LENGTH ns) /\ (LENGTH ns = LENGTH zs) ==>
      (mw_monprod5 xs ys ns m zs q = FRONT (mw_monprod4 xs ys ns m (zs ++ [q])))``,
  REWRITE_TAC [mw_monprod4_def,mw_monprod5_def]
  \\ SIMP_TAC bool_ss [mw_monmult4_EQ_mw_monmult5,LESS_EQ_REFL]
  \\ REPEAT STRIP_TAC 
  \\ `LENGTH (FST (mw_monmult5 xs ys ns m zs q)) = LENGTH zs` by
       (MATCH_MP_TAC LENGTH_mw_monmult5 \\ ASM_REWRITE_TAC [LESS_EQ_REFL])
  \\ Cases_on `mw_monmult5 xs ys ns m zs q`
  \\ FULL_SIMP_TAC std_ss [LET_DEF,mw_sub_APPEND,FST]
  \\ REWRITE_TAC [mw_sub_def]
  \\ Q.SPEC_TAC (`mw_sub q' ns T`,`ddd`) \\ Cases \\ SIMP_TAC std_ss [LET_DEF]
  \\ Q.SPEC_TAC (`single_sub r 0w r'`,`ddd`) \\ Cases \\ SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `r'` \\ REWRITE_TAC [BUTLAST,GSYM SNOC_APPEND]);

val mw_monprod5_spec = prove(
  ``2 < dimword (:'a) ==> 
    !t u n n' r' i.
      montprod_vars n n' (dimwords i (:'a)) r' t u ==>
      (mw_monprod5 (n2mw i t) (n2mw i u) (n2mw i n) (n2w n') (n2mw i 0) 0w =
       n2mw i ((t * u * r') MOD n) :('a word) list)``,
  SIMP_TAC bool_ss [LENGTH_n2mw,mw_monprod_5_EQ_4]
  \\ REWRITE_TAC [GSYM (REWRITE_CONV [n2mw_def] ``n2mw (SUC 0) 0``),n2mw_APPEND]
  \\ SIMP_TAC bool_ss [ZERO_LT_dimwords,LESS_MOD,MULT_CLAUSES,ADD_CLAUSES]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC mw_monprod4_spec
  \\ ASM_SIMP_TAC bool_ss [ADD1]
  \\ Q.SPEC_TAC (`(t * u * r') MOD n`,`p`) \\ POP_ASSUM_LIST (fn thm => ALL_TAC)
  \\ Induct_on `i` THEN1 REWRITE_TAC [FRONT_DEF,n2mw_def,GSYM ADD1]
  \\ ASM_REWRITE_TAC [ADD_CLAUSES,n2mw_def,FRONT_DEF]
  \\ REWRITE_TAC [GSYM ADD1,n2mw_def,NOT_CONS_NIL]);


(* optimisation 3: unroll to get rid of the 0 input *)

val mw_moninit_def = Define `
  mw_moninit ys ns x m =  mw_monmult5_step ys ns (MAP (\x. 0w) ys) 0w x m`;

val mw_monprod6_def = Define `
  mw_monprod6 (x::xs) ys ns m = 
    let (zs,z) = mw_moninit ys ns x m in
    let (zs,z) = mw_monmult5 xs ys ns m zs z in
    let (zs',c) = mw_sub zs ns T in
    let c' = SND (single_sub z 0w c) in
      (if c' then zs' else zs)`;

val mw_monprod_6_EQ_5 = prove( 
  ``!xs ys ns m q.
      0 < LENGTH xs /\
      (LENGTH xs = LENGTH ys) /\ (LENGTH ys = LENGTH ns) ==>
      (mw_monprod6 xs ys ns m = mw_monprod5 xs ys ns m (MAP (\x. 0w) ys) 0w)``,
  Cases \\ REWRITE_TAC [EVAL ``0<0``,LENGTH]  
  \\ REWRITE_TAC [mw_monprod6_def,mw_monprod5_def]
  \\ NTAC 2 (Cases THEN1 SIMP_TAC bool_ss [LENGTH,DECIDE ``~(SUC n <= 0) /\ ~(SUC n = 0)``])
  \\ REWRITE_TAC [mw_monmult5_def,MAP,mw_moninit_def] \\ STRIP_TAC
  \\ Q.SPEC_TAC (`mw_monmult5_step (h'::t') (h''::t'') (0w::MAP (\x. 0w) t') 0w h m`,`ddd`)
  \\ Cases \\ SIMP_TAC std_ss [LET_DEF]);

val mw_monprod6_spec = store_thm("mw_monprod6_spec",
  ``2 < dimword (:'a) ==> 
    !t u n n' r' i.
      montprod_vars n n' (dimwords i (:'a)) r' t u /\ 0 < i ==>
      (mw_monprod6 (n2mw i t) (n2mw i u) (n2mw i n) (n2w n') =
       n2mw i ((t * u * r') MOD n) :('a word) list)``,
  REPEAT STRIP_TAC
  \\ `0 < LENGTH (n2mw i t)` by FULL_SIMP_TAC bool_ss [LENGTH_n2mw]
  \\ ASM_SIMP_TAC bool_ss [LENGTH_n2mw,mw_monprod_6_EQ_5]
  \\ `!i u. MAP (\x. 0w) (n2mw i u :('a word) list) = n2mw i 0:('a word) list`
       by (Induct \\ ASM_SIMP_TAC bool_ss [MAP,n2mw_def,ZERO_DIV,ZERO_LT_dimword])
  \\ ASM_SIMP_TAC bool_ss [mw_monprod5_spec]);

val mw_add_mul_mult0_def = Define `
  (mw_add_mul_mult0 [] ys p q c b = ([],c,b): (('a word) list) # ('a word) # ('a word)) /\
  (mw_add_mul_mult0 xs [] p q c b = ([],c,b): (('a word) list) # ('a word) # ('a word)) /\
  (mw_add_mul_mult0 (x::xs) (y::ys) p q c b = 
    let (w,c1,b1) = add_double_mul x y p q c b 0w in
    let (ws,c2,b2) = mw_add_mul_mult0 xs ys p q c1 b1 in
      (w :: ws,c2,b2))`;

val mw_add_mul_mult0_spec = store_thm("mw_add_mul_mult0_spec",
  ``!xs ys p q c b.
      mw_add_mul_mult xs ys (MAP (\x.0w) xs) p q c b = 
      mw_add_mul_mult0 xs ys p q c b``,
  Induct \\ Cases_on `ys` 
  \\ ASM_REWRITE_TAC [mw_add_mul_mult_def,mw_add_mul_mult0_def,MAP]);

val mw_add_mul_mult0_cases = cases_thm "mw_add_mul_mult0_cases" [mw_add_mul_mult0_def]
    [``FST (mw_add_mul_mult0 [] [] p q c b)``,
     ``SND (mw_add_mul_mult0 [] [] p q c b)``,
     ``FST (mw_add_mul_mult0 (x::xs) (y::ys) p q c b)``,
     ``SND (mw_add_mul_mult0 (x::xs) (y::ys) p q c b)``]

val add_double_mul_thm = store_thm("add_double_mul_thm",
  ``!x y p q c b z:'a word.
      add_double_mul x y p q c b z =
        let (x1,x2) = single_mul x p z in
        let (x3,x4) = single_mul y q x1 in
        let (x5,c1) = single_add x3 c F in
        let (x6,c2) = single_add x2 b c1 in
        let (x7,c3) = single_add 0w 0w c2 in
        let (x8,c4) = single_add x4 x6 F in
        let (x9,c5) = single_add x7 0w c4 in
          (x5,x8,x9)``,
  `n2w (dimword (:'a)) = 0w:'a word` by
    (ONCE_REWRITE_TAC [GSYM n2w_mod] \\ SIMP_TAC bool_ss [DIVMOD_ID,ZERO_LT_dimword,LESS_MOD])
  \\ ASM_SIMP_TAC std_ss [add_double_mul_def,n2w_w2n,single_mul_def,WORD_MULT_CLAUSES,
    GSYM word_add_n2w,GSYM word_mul_n2w,single_add_def,LET_DEF,b2w_def,b2n_def,WORD_ADD_0]
  \\ NTAC 7 Cases_word \\ ASM_SIMP_TAC std_ss [w2n_n2w,LESS_MOD,word_add_n2w,word_mul_n2w]
  \\ STRIP_TAC THEN1 SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM,AC MULT_ASSOC MULT_COMM]
  \\ `!n. n MOD dimword (:'a) < dimword (:'a)` by 
        ASM_SIMP_TAC bool_ss [GSYM DIVISION, ZERO_LT_dimword]
  \\ `!m n k. m < k /\ n < k ==> m + n < k + k:num` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [ADD_CARRY_LEMMA,ZERO_LT_dimword]    
  \\ (CONV_TAC o BINOP_CONV o RATOR_CONV o RAND_CONV)
    (ONCE_REWRITE_CONV [DECIDE 
       ``m + n * n'' + j * i + k + l * g:num = (n * n'' + m) + j * i + k + l * g``])
  \\ `n' * n''' + (n * n'' + n'''''') MOD dimword (:'a) < dimword (:'a) * dimword (:'a)`
    by (MATCH_MP_TAC MULT_ADD_LESS_MULT 
    \\ ASM_SIMP_TAC bool_ss [LESS_IMP_LESS_OR_EQ,GSYM DIVISION,ZERO_LT_dimword])
  \\ `n * n'' + n'''''' < dimword (:'a) * dimword (:'a)` by
    (MATCH_MP_TAC MULT_ADD_LESS_MULT \\ ASM_SIMP_TAC bool_ss [LESS_IMP_LESS_OR_EQ])
  \\ Q.ABBREV_TAC `g = n * n'' + n''''''` \\ Q.ABBREV_TAC `h = n' * n'''`
  \\ Q.ABBREV_TAC `c = n''''` \\ Q.ABBREV_TAC `b = n'''''`
  \\ REWRITE_TAC [ADD_ASSOC] \\ STRIP_TAC << [
    ONCE_REWRITE_TAC [DECIDE ``hg+g+b+xx =b+xx+(g + hg):num``]
    \\ SIMP_TAC bool_ss [GSYM ADD_DIV_ADD_DIV,ZERO_LT_dimword]
    \\ ONCE_REWRITE_TAC [DECIDE ``n DIV j * j +(m + k MOD j):num = m+(n DIV j * j + k MOD j)``]
    \\ SIMP_TAC bool_ss [GSYM DIVISION,ZERO_LT_dimword]    
    \\ SIMP_TAC bool_ss [ADD_DIV_ADD_DIV,ZERO_LT_dimword]
    \\ SIMP_TAC bool_ss [GSYM(RW1[ADD_COMM]ADD_DIV_ADD_DIV),ZERO_LT_dimword,GSYM ADD_ASSOC]
    \\ ONCE_REWRITE_TAC [DECIDE ``hg MOD j + (c + hg DIV j *j) = c + (hg DIV j*j + hg MOD j)``]
    \\ SIMP_TAC bool_ss [GSYM DIVISION,ZERO_LT_dimword]
    \\ SIMP_TAC bool_ss [GSYM ADD_DIV_ADD_DIV,ZERO_LT_dimword]
    \\ SIMP_TAC bool_ss [AC ADD_COMM ADD_ASSOC,AC MULT_COMM MULT_ASSOC],  
    `((h + g) MOD dimword (:'a) + c) DIV dimword (:'a) < 2` by
      (SIMP_TAC bool_ss [DIV_LT_X,ZERO_LT_dimword,TIMES2]      
       \\ MATCH_MP_TAC (DECIDE ``m < k /\ n < k ==> m + n < k + k:num``)
       \\ Q.UNABBREV_TAC `c` \\ ASM_SIMP_TAC bool_ss [])
    \\ `((g DIV dimword (:'a)) MOD dimword (:'a) + b + ((h + g) MOD dimword (:'a) + c) 
      DIV dimword (:'a)) < dimword(:'a) + dimword(:'a)` by
       ASM_SIMP_TAC bool_ss [DECIDE ``i < k /\ j < k /\ p < 2 ==> j + i + p < k + k:num``]
    \\ ASM_SIMP_TAC bool_ss [ADD_CARRY_LEMMA,ZERO_LT_dimword]
    \\ ASM_SIMP_TAC bool_ss [DIV_MOD_MOD_DIV,ZERO_LT_dimword,LESS_MOD]
    \\ Q.ABBREV_TAC `i = (g DIV dimword (:'a) + b +
        ((h + g) MOD dimword (:'a) + c) DIV dimword (:'a))`  
    \\ SIMP_TAC bool_ss [GSYM ADD_DIV_ADD_DIV,ZERO_LT_dimword]
    \\ ONCE_REWRITE_TAC [DECIDE ``i DIV j*j + (x+i MOD j)=x+(i DIV j*j + i MOD j)``]
    \\ SIMP_TAC bool_ss [GSYM DIVISION,ZERO_LT_dimword]
    \\ SIMP_TAC bool_ss [RW1[ADD_COMM](GSYM ADD_DIV_ADD_DIV),ZERO_LT_dimword,GSYM DIV_DIV_DIV_MULT]
    \\ Q.UNABBREV_TAC `i` \\ REWRITE_TAC [RIGHT_ADD_DISTRIB,ADD_ASSOC]
    \\ ONCE_REWRITE_TAC [DECIDE ``h+g MOD j +g DIV j*j+b+x=(g DIV j*j + g MOD j)+h+b+x:num``]
    \\ SIMP_TAC bool_ss [GSYM DIVISION,ZERO_LT_dimword]
    \\ SIMP_TAC bool_ss [RW1[ADD_COMM]ADD_DIV_ADD_DIV,ADD_ASSOC,ZERO_LT_dimword]    
    \\ SIMP_TAC bool_ss [GSYM ADD_DIV_ADD_DIV,RIGHT_ADD_DISTRIB,ZERO_LT_dimword]    
    \\ SIMP_TAC bool_ss [RW1[ADD_COMM](GSYM ADD_DIV_ADD_DIV),ADD_ASSOC,ZERO_LT_dimword]    
    \\ ONCE_REWRITE_TAC [DECIDE ``m DIV j*j+b+(h+g)MOD j+c=(m DIV j*j + (h+g)MOD j)+c+b``]
    \\ ONCE_REWRITE_TAC [METIS_PROVE[ADD_COMM]``(h+g) MOD j= (g+h) MOD j``]
    \\ SIMP_TAC bool_ss [GSYM DIVISION,ZERO_LT_dimword]]);

fun cases_thm name thm tms = 
  save_thm(name,(RW [] o foldr (uncurry CONJ) TRUTH o (map (EXPAND_LET_CONV thm))) tms);

val add_double_mul_cases = cases_thm "add_double_mul_cases" [add_double_mul_thm] 
    [``FST (add_double_mul x y p q c b z)``,
     ``FST (SND (add_double_mul x y p q c b z))``,
     ``SND (SND (add_double_mul x y p q c b z))``];

val add_double_mul_000 = store_thm("add_double_mul_000",
  ``!p q c b. add_double_mul 0w 0w p q c b 0w = (c,b,0w)``,
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [add_double_mul_def,word_0_n2w,MULT_CLAUSES,ADD_CLAUSES]
  \\ ONCE_REWRITE_TAC [ADD_COMM] \\ SIMP_TAC bool_ss [LET_DEF,PAIR_EQ]
  \\ SIMP_TAC bool_ss [DIV_MULT,w2n_lt,n2w_w2n] \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ SIMP_TAC bool_ss [MOD_MULT,w2n_lt,n2w_w2n] \\ ONCE_REWRITE_TAC [n2w_mod]
  \\ `w2n b * dimword (:'a) + w2n c < dimword (:'a) * dimword (:'a)` by ALL_TAC
  \\ ASM_SIMP_TAC bool_ss [LESS_DIV_EQ_ZERO]
  \\ MATCH_MP_TAC MULT_ADD_LESS_MULT \\ REWRITE_TAC [w2n_lt,LESS_EQ_REFL]);

val single_add_0F = prove(
  ``!x. (single_add x 0w F = (x,F)) /\ (single_add 0w x F = (x,F))``,
  REWRITE_TAC [single_add_def,b2n_def,b2w_def,WORD_ADD_0,ADD,
    word_0_n2w,ADD_0,w2n_lt,DECIDE ``n<=m = ~(m<n:num)``]);

val single_mul_0 = prove(
  ``!x. (single_mul x 0w y = (y,0w)) /\ (single_mul 0w x y = (y,0w))``,
  SIMP_TAC bool_ss [single_mul_def,WORD_MULT_CLAUSES,
    WORD_ADD_0,word_0_n2w,MULT_CLAUSES,ADD_CLAUSES,w2n_lt,LESS_DIV_EQ_ZERO]);

val add_double_mul_00 = store_thm("add_double_mul_00",
  ``!x y p q z.
      add_double_mul x y p q 0w 0w z =
        let (x1,x2) = single_mul x p z in
        let (x3,x4) = single_mul y q x1 in
        let (x8,c4) = single_add x4 x2 F in
        let (x9,c5) = single_add 0w 0w c4 in
          (x3,x8,x9)``,
  SIMP_TAC std_ss [add_double_mul_thm,single_add_0F,LET_DEF]);

val add_double_mul_00_cases = cases_thm "add_double_mul_00_cases" [add_double_mul_00] 
    [``FST (add_double_mul x y p q 0w 0w z)``,
     ``FST (SND (add_double_mul x y p q 0w 0w z))``,
     ``SND (SND (add_double_mul x y p q 0w 0w z))``];

val add_double_mul_x00 = store_thm("add_double_mul_x00",
  ``!p q c b z.
      add_double_mul 0w 0w p q c b z =
        let (x5,c1) = single_add z c F in
        let (x6,c2) = single_add b 0w c1 in
        let (x7,c3) = single_add 0w 0w c2 in
          (x5,x6,x7)``,
  SIMP_TAC std_ss [add_double_mul_thm,single_add_0F,LET_DEF,single_mul_0]
  \\ REWRITE_TAC [single_add_def,word_0_n2w,ADD,WORD_ADD_0,ADD_0]);

val add_double_mul_x00_cases = cases_thm "add_double_mul_x00_cases" [add_double_mul_x00,single_add_0F] 
    [``FST (add_double_mul 0w 0w p q c b z)``,
     ``FST (SND (add_double_mul 0w 0w p q c b z))``,
     ``SND (SND (add_double_mul 0w 0w p q c b z))``];

val add_double_mul_x000_cases = cases_thm "add_double_mul_x000_cases" [add_double_mul_x00,single_add_0F] 
    [``FST (add_double_mul 0w 0w p q c b 0w)``,
     ``FST (SND (add_double_mul 0w 0w p q c b 0w))``,
     ``SND (SND (add_double_mul 0w 0w p q c b 0w))``];

val mw_monmult5_step_cases = cases_thm' "mw_monmult5_step_cases" [mw_monmult5_step_def] [add_double_mul_x000_cases]
  [``FST (mw_monmult5_step (x::xs) (y::ys) (z::zs) z' p m)``,
   ``SND (mw_monmult5_step (x::xs) (y::ys) (z::zs) z' p m)``]

val mw_monmult5_cases = cases_thm "mw_monmult5_cases" [mw_monmult5_def]
  [``FST (mw_monmult5 [] ys ns m zs x)``,
   ``SND (mw_monmult5 [] ys ns m zs x)``,
   ``FST (mw_monmult5 (x::xs) (y::ys) (n::ns) m (z::zs) z')``,
   ``SND (mw_monmult5 (x::xs) (y::ys) (n::ns) m (z::zs) z')``]

val LENGTH_FST_mw_moninit = store_thm("LENGTH_FST_mw_moninit",
  ``~(0 = LENGTH xs) /\ (LENGTH ys = LENGTH xs) ==>
    (LENGTH (FST (mw_moninit xs ys p q)) = LENGTH xs)``,
  Cases_on `xs` \\ Cases_on `ys` \\ REWRITE_TAC [LENGTH] \\ REPEAT DECIDE_TAC
  \\ REPEAT STRIP_TAC \\ REWRITE_TAC [GSYM (REWRITE_CONV [LENGTH] ``LENGTH (h::t)``)]
  \\ REWRITE_TAC [mw_moninit_def,MAP] \\ MATCH_MP_TAC LENGTH_FST_mw_monmult5_step 
  \\ FULL_SIMP_TAC bool_ss [ADD1,EQ_ADD_RCANCEL,LENGTH_MAP]);

val mw_monprod6_cases = cases_thm "mw_monprod6_cases" [mw_monprod6_def]
  [``mw_monprod6 (x::xs) ys ns m``]


(* binary exponential *)
  
val word_right_shift_n2w = prove(
  ``!n k. (n2w n):'a word >>> k = n2w ((n MOD dimword (:'a)) DIV 2**k)``,
  REWRITE_TAC [word_lsr_n2w,word_bits_n2w,MIN_DEF,DECIDE ``~(n<n:num)``]
  \\ REWRITE_TAC [BITS_THM2,dimword_def]
  \\ `0 < dimindex(:'a)` by REWRITE_TAC [DIMINDEX_GT_0]
  \\ Cases_on `dimindex(:'a)` THEN1 `F` by DECIDE_TAC
  \\ ASM_REWRITE_TAC [ADD1,ADD_SUB]);

val (exp_last_def,exp_last_ind) = Defn.tprove(Defn.Hol_defn "exp_last_def" `
  exp_last f x m n = if x = 0w then m else
                       let m' = if x && 1w = 0w then m else f m n in
                         exp_last f (x >>> 1) m' (f n n)`,
  WF_REL_TAC `measure (w2n o FST o SND)` \\ Cases_word
  \\ REWRITE_TAC [word_right_shift_n2w,EVAL ``2**1``]  
  \\ ASM_SIMP_TAC bool_ss [n2w_11,w2n_n2w,LESS_MOD,ZERO_LT_dimword]
  \\ REPEAT STRIP_TAC \\ `n DIV 2 < n` by 
       (SIMP_TAC std_ss [DIV_LT_X,RW1[MULT_COMM]TIMES2] \\ DECIDE_TAC)
  \\ IMP_RES_TAC LESS_TRANS \\ ASM_SIMP_TAC bool_ss [LESS_MOD]);

val (exp_step3_def,exp_step3_ind) = Defn.tprove(Defn.Hol_defn "exp_step3_def" `
  exp_step3 f (i:'a word) (x:'a word) (m:'v) n =
    if i = 0w then (m,n) else
      let m = if x && 1w = 0w then m else f m n in
        exp_step3 f (i-1w) (x >>> 1) m (f n n)`,
  WF_REL_TAC `measure (w2n o FST o SND)` \\ REWRITE_TAC [WORD_PRED_THM]);

val exp_step4_def = Define `
  exp_step4 f x m n = exp_step3 f (n2w (dimindex(:'a))) (x:'a word) (m:'v) n`;

val MULT_EXP = prove(
  ``!k m. (k * k) ** m = k ** (2 * m)``,
  REWRITE_TAC [EXP_BASE_MULT,TIMES2,EXP_ADD]);

val SUC_TWO_TIMES_DIV_TWO = prove(
  ``!m. SUC (2 * m) DIV 2 = m``,
  SIMP_TAC std_ss [EQ_LESS_EQ,DIV_LE_X,X_LE_DIV,TIMES2,RW1[MULT_COMM]TIMES2]
  \\ DECIDE_TAC);

val ODD_LEMMA = prove(
  ``!n. ODD n ==> (SUC (2 * (n DIV 2)) = n)``,
  REWRITE_TAC [ODD_EXISTS] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [SUC_TWO_TIMES_DIV_TWO]);
  
val NOT_ODD_LEMMA = prove(
  ``!n. ~ODD n ==> (2 * (n DIV 2) = n)``,
  REWRITE_TAC [ODD_EVEN,EVEN_EXISTS] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [RW1[MULT_COMM]MULT_DIV]);
  
val exp_step_lemma1 = prove(
  ``!m i. 2 * (2 * m DIV 2) MOD 2 ** i = (2 * m) MOD 2 ** SUC i``,
  SIMP_TAC std_ss [RW1[MULT_COMM]MULT_DIV,EXP,MOD_COMMON_FACTOR,ZERO_LT_EXP]);

val exp_step_lemma2 = prove(
  ``!m i. SUC (2 * (SUC (2 * m) DIV 2) MOD 2 ** i) = SUC (2 * m) MOD 2 ** SUC i``,
  REWRITE_TAC [SUC_TWO_TIMES_DIV_TWO] 
  \\ REWRITE_TAC [EXP] \\ REWRITE_TAC [ADD1] \\ REPEAT STRIP_TAC
  \\ `0 < 2 * 2 ** i` by ASM_SIMP_TAC std_ss [ZERO_LESS_MULT,ZERO_LT_EXP]
  \\ IMP_RES_TAC (GSYM MOD_PLUS) \\ ONCE_ASM_REWRITE_TAC []
  \\ `0 < 2 ** i` by SIMP_TAC std_ss [ZERO_LT_EXP]
  \\ `1 < 2 * 2 ** i` by (REWRITE_TAC [TIMES2] \\ DECIDE_TAC)
  \\ Q.PAT_ASSUM `!x.b` (fn th => ALL_TAC)
  \\ ASM_SIMP_TAC std_ss [LESS_MOD,GSYM MOD_COMMON_FACTOR]  
  \\ MATCH_MP_TAC (RW1[MULT_COMM]MULT_ADD_LESS_MULT)   
  \\ ASM_SIMP_TAC std_ss [GSYM DIVISION]);
  
val n2w_and_1w = prove(
  ``!n. n2w n && 1w = n2w (n MOD 2)``,
  SIMP_TAC bool_ss [word_and_n2w,fcpTheory.CART_EQ]
  \\ ONCE_REWRITE_TAC [word_index_n2w]
  \\ SIMP_TAC bool_ss [BITWISE_THM]
  \\ STRIP_TAC \\ Cases << [  
    REWRITE_TAC [BIT_def,BITS_THM]
    \\ REWRITE_TAC [EXP,DIV_1,EVAL ``2**(SUC 0-0)``]
    \\ SIMP_TAC std_ss [EVAL ``1<2``,LESS_MOD,MOD_MOD],
    REWRITE_TAC [BIT_def,BITS_THM2]
    \\ `n MOD 2 < 2` by SIMP_TAC std_ss [GSYM DIVISION]
    \\ REWRITE_TAC [EXP,TIMES2,ADD_ASSOC]
    \\ `0 < 2**n'` by SIMP_TAC std_ss [ZERO_LT_EXP] 
    \\ Q.ABBREV_TAC `k = 2**n'`
    \\ `n MOD 2 < k+k /\ 1 < k+k` by DECIDE_TAC
    \\ `n MOD 2 < k+k+k+k /\ 1 < k+k+k+k` by DECIDE_TAC
    \\ ASM_SIMP_TAC bool_ss [LESS_MOD,LESS_DIV_EQ_ZERO,EVAL ``0=1``]]);
    
val WORD_EQ_EVEN = prove(
  ``!x. (x && 1w = 0w) = EVEN (w2n x)``,
  Cases_word \\ ASM_SIMP_TAC bool_ss [n2w_and_1w,w2n_n2w,LESS_MOD]
  \\ Cases_on `EVEN n` \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC bool_ss [GSYM ODD_EVEN]
  \\ FULL_SIMP_TAC bool_ss [EVEN_EXISTS,ODD_EXISTS,ADD1]
  \\ ONCE_REWRITE_TAC [MULT_COMM]  
  \\ SIMP_TAC std_ss [REWRITE_RULE [ADD_0] (Q.SPECL [`n`,`0`] MOD_MULT)]
  \\ SIMP_TAC std_ss [MOD_TIMES]
  \\ SIMP_TAC bool_ss [n2w_11,ONE_LT_dimword,ZERO_LT_dimword,LESS_MOD]
  \\ DECIDE_TAC);

val exp_last_spec = prove(
  ``!x:'a word f g i m k. 
      (!m n. f (g m) (g n) = g (m * n)) ==>  
      (exp_last f x (g m) (g k) = g (m * k ** w2n x))``,
  Cases_word \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD]
  \\ completeInduct_on `n` \\ Cases_on `n` 
  \\ ONCE_REWRITE_TAC [exp_last_def] \\ SIMP_TAC bool_ss 
       [EXP,MULT_CLAUSES,DECIDE ``~(SUC n = 0)``,n2w_11,LESS_MOD,ZERO_LT_dimword]
  \\ SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC 
  \\ ASM_SIMP_TAC bool_ss [WORD_EQ_EVEN,w2n_n2w,LESS_MOD,word_right_shift_n2w]
  \\ `SUC n' DIV 2 < SUC n'` by (MATCH_MP_TAC DIV_LESS \\ DECIDE_TAC)
  \\ `SUC n' DIV 2 < dimword (:'a)` by DECIDE_TAC
  \\ RES_TAC \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
  \\ Cases_on `EVEN (SUC n')` \\ ASM_REWRITE_TAC [MULT_EXP,EVAL ``2**1``] 
  \\ FULL_SIMP_TAC bool_ss [EVEN_ODD]
  \\ ASM_SIMP_TAC bool_ss [GSYM MULT_ASSOC,GSYM EXP,ODD_LEMMA,NOT_ODD_LEMMA]);  

val exp_step3_spec = prove(
  ``!i:'a word x f g m k. 
      (!m n. f (g m) (g n) = g (m * n)) ==>  
      (exp_step3 f i x (g m) (g k) = 
       (g (m * k ** (w2n x MOD 2 ** w2n i)), g (k ** (2 ** w2n i))))``,
  Cases_word \\ Cases_word \\ ASM_SIMP_TAC bool_ss [w2n_n2w,LESS_MOD]
  \\ Q.UNDISCH_TAC `n' < dimword (:'a)` \\ Q.SPEC_TAC (`n'`,`j`)
  \\ Induct_on `n` \\ ONCE_REWRITE_TAC [exp_step3_def]
  \\ REWRITE_TAC [EXP,MOD_1,MULT_CLAUSES]
  \\ ASM_REWRITE_TAC [GSYM (EVAL ``SUC 0``),MULT_CLAUSES,ADD_0,EXP]
  \\ REWRITE_TAC [EVAL ``SUC 0``,WORD_EQ_EVEN,word_right_shift_n2w,EVAL ``2**1``]
  \\ SIMP_TAC bool_ss [LESS_MOD,w2n_n2w,n2w_11,ZERO_LT_dimword]
  \\ REWRITE_TAC [DECIDE ``~(SUC n = 0)``]
  \\ SIMP_TAC std_ss [LET_DEF,MULT_EXP] \\ REPEAT STRIP_TAC
  \\ `j DIV 2 <= j` by (SIMP_TAC std_ss [DIV_LE_X,GSYM ADD1,MULT]
       \\ REWRITE_TAC [RW1[MULT_COMM]TIMES2] \\ DECIDE_TAC)
  \\ REWRITE_TAC [ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ `n < dimword (:'a)` by DECIDE_TAC
  \\ `j DIV 2 < dimword (:'a)` by IMP_RES_TAC LESS_EQ_LESS_TRANS
  \\ Q.PAT_ASSUM `bbbb ==> bbb` 
        (STRIP_ASSUME_TAC o UNDISCH o Q.SPEC `j DIV 2` o UNDISCH)
  \\ RES_TAC \\ REWRITE_TAC [EVEN_ODD] \\ Cases_on `ODD j` 
  \\ ASM_REWRITE_TAC [MULT_EXP,GSYM EXP,GSYM MULT_ASSOC,PAIR_EQ]
  \\ FULL_SIMP_TAC bool_ss [GSYM EVEN_ODD]
  \\ FULL_SIMP_TAC bool_ss [EVEN_EXISTS,ODD_EXISTS,GSYM EXP]
  \\ REWRITE_TAC [exp_step_lemma1,exp_step_lemma2]);

val LESS_TWO_EXP = prove(
  ``!n. n < 2 ** n``,
  Induct THEN1 EVAL_TAC \\ REWRITE_TAC [EXP,TIMES2]
  \\ `0 < 2 ** n` by SIMP_TAC std_ss [ZERO_LT_EXP] \\ DECIDE_TAC);

val TWO_EXP_w2n_n2w_dimindex = prove(
  ``2 ** w2n ((n2w (dimindex (:'a))):'a word) = dimword (:'a)``,
  SIMP_TAC bool_ss [w2n_n2w,LESS_TWO_EXP,dimword_def,LESS_MOD]);

val exp_step4_spec = 
  SIMP_RULE bool_ss [TWO_EXP_w2n_n2w_dimindex,LESS_MOD,w2n_lt,GSYM exp_step4_def] 
    (Q.SPECL [`n2w (dimindex(:'a))`] exp_step3_spec);

val exp_list_def = Define `
  (exp_list f m n [] = (m,n)) /\
  (exp_list f m n (x::xs) = 
     let (m,n) = exp_step4 f x m n in exp_list f m n xs)`;
  
val exp_list_spec = prove(
  ``!i n f g m k. 
      (!m n. f (g m) (g n) = g (m * n)) ==>  
      (exp_list f (g m) (g k) ((n2mw i n):('a word) list) = 
        (g (m * k ** (n MOD dimwords i (:'a))), g (k ** dimwords i (:'a))))``,
  Induct
  \\ REWRITE_TAC [exp_list_def,n2mw_def,MOD_1,EXP,MULT_CLAUSES,dimwords_def]
  \\ REWRITE_TAC [GSYM (EVAL ``SUC 0``),ADD_CLAUSES,EXP,MULT_CLAUSES]
  \\ SIMP_TAC bool_ss [exp_step4_spec]
  \\ SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC      
  \\ RES_TAC \\ ASM_REWRITE_TAC [PAIR_EQ,w2n_n2w]  
  \\ REWRITE_TAC [GSYM EXP_EXP_MULT]
  \\ REWRITE_TAC [GSYM MULT_ASSOC,GSYM EXP_ADD]
  \\ REWRITE_TAC [MULT_ASSOC]
  \\ SIMP_TAC bool_ss [ZERO_LT_dimwords,ZERO_LT_dimword,DIV_MOD_MOD_DIV]
  \\ REWRITE_TAC [GSYM MULT,GSYM dimwords_def]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ `n MOD dimword (:'a) = 
       (n MOD (dimword (:'a) * dimwords i (:'a))) MOD dimword (:'a)` 
       by  SIMP_TAC bool_ss [MOD_MULT_MOD,ZERO_LT_dimwords,ZERO_LT_dimword]
  \\ ONCE_ASM_REWRITE_TAC []
  \\ SIMP_TAC bool_ss [RW1 [MULT_COMM] (GSYM DIVISION),ZERO_LT_dimword]
  \\ REWRITE_TAC [RW1[MULT_COMM]dimwords_SUC]);

val exp_list_last_def = Define `
  exp_list_last f m n xs = 
    let (m,n) = exp_list f m n (FRONT xs) in
      exp_last f (LAST xs) m n`;

val exp_list_last_spec = prove(
  ``!i n f g m k. 
      (!m n. f (g m) (g n) = g (m * n)) /\ 0 < i ==>  
      (exp_list_last f (g m) (g k) ((n2mw i n):('a word) list) = 
        g (m * k ** (n MOD dimwords i (:'a))))``,
  Cases_on `i` \\ REWRITE_TAC [DECIDE ``~(0<0)``]
  \\ REWRITE_TAC [exp_list_last_def,n2mw_SNOC,LAST,BUTLAST]
  \\ SIMP_TAC std_ss [exp_last_spec,exp_list_spec,LET_DEF]
  \\ REWRITE_TAC [GSYM MULT_ASSOC,GSYM EXP_ADD,GSYM EXP_EXP_MULT,w2n_n2w]
  \\ SIMP_TAC bool_ss [ZERO_LT_dimwords,ZERO_LT_dimword,DIV_MOD_MOD_DIV]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ `!n i. n MOD dimwords i (:'a) = 
       (n MOD (dimwords i (:'a) * dimword (:'a))) MOD dimwords i (:'a)` 
       by  SIMP_TAC bool_ss [MOD_MULT_MOD,ZERO_LT_dimwords,ZERO_LT_dimword]
  \\ ONCE_ASM_REWRITE_TAC []
  \\ SIMP_TAC bool_ss [RW1 [MULT_COMM] (GSYM DIVISION),ZERO_LT_dimwords]
  \\ SIMP_TAC bool_ss [MOD_MULT_MOD,ZERO_LT_dimword,ZERO_LT_dimwords]
  \\ REWRITE_TAC [dimwords_SUC]);



val _ = export_theory();

