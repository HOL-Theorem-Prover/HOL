
(* 
  set_trace "pp_unambiguous_comprehensions" 1;
*)

open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory wordsTheory arithmeticTheory listTheory;

open set_sepTheory set_sepLib;


val _ = new_theory "prog";

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val PAIR_EQ = pairTheory.PAIR_EQ;


(* ----------------------------------------------------------------------------- *)
(* Definitions                                                                   *)
(* ----------------------------------------------------------------------------- *)

val _ = type_abbrev("processor",
  ``:('a set set)#
     ('a set -> 'a set)#
     ('b word -> 'a set -> bool)#
     ('b word # 'c -> 'a set -> bool)``);

val PROCESSORS_def = Define `
  PROCESSORS = 
    { (Z,next,pc,inst) |(Z,next,pc,inst)| !s::Z. (next s) IN Z } 
      : ('a,'b,'c) processor set`;

val run_def = Define `
  (run next (0,s) = s) /\ 
  (run next (SUC k,s) = run next (k, next s))`;

val RUN_def = Define `
  RUN (set,n,p,i) P Q = !(s::set) R. (P * R) s ==> ?k. (Q * R) (run n (k,s))`;

val msequence_def = Define `
  (msequence i a [] = emp) /\ 
  (msequence i a (x::xs) = i (a,x) * msequence i (a+1w) xs)`;

val mset_def = Define `
  mset i p (cs,f) = { i (f p + n2w k,c) |(c,k)| k < LENGTH cs /\ (c = EL k cs) }`;

val mpool_def = Define `
  mpool i p Z = BIGSTAR (BIGUNION { mset i p z |z| z IN Z })`;

val wLENGTH_def = Define `wLENGTH cs = n2w (LENGTH cs)`;

val pcSET_def = Define `pcSET x = \p. x:bool**'a`;
val pcADD_def = Define `pcADD n = \p. n + p`;
val pcINC_def = Define `pcINC c = pcADD (wLENGTH c)`;

val setAPP_def = Define `setAPP g Z = { (Q,f o g) |(Q,f)| (Q,f) IN Z }`;
val setADD_def = Define `setADD k Z = setAPP (pcADD k) Z`;
val setINC_def = Define `setINC c Z = setADD (wLENGTH c) Z`;
val setSTAR_def = Define `setSTAR (R:'a set ->bool) Z = { (Q * R,f) |(Q,f)| (Q,f) IN Z }`;

val GPROG_def = Define `
  GPROG ((set,n,pc,i):('a,'b,'c)processor) (Y:(('a set->bool)#('b word->'b word)) set) C Z =
    !p. RUN (set,n,pc,i) 
           (SEP_BIGDISJ { P * mpool i p C * pc (f p) | (P,f) IN Y })
           (SEP_BIGDISJ { Q * mpool i p C * pc (f p) | (Q,f) IN Z })`;

val PROG_def = Define `
  PROG ((set,n,pc,i):('a,'b,'c)processor) P cs C Q Z =
    GPROG (set,n,pc,i) {(P,I)} ((cs,I) INSERT C) ((Q,pcINC cs) INSERT Z)`;

val PROC_def = Define `
  PROC ((set,n,pc,i):('a,'b,'c)processor) lr P Q C =
    !q. PROG (set,n,pc,i) (P * lr q) [] C SEP_F {(Q,pcSET q)}`;

val CALL_def = Define `
  CALL ((set,n,pc,i):('a,'b,'c)processor) lr P cs f = 
    !p. RUN (set,n,pc,i) 
          (P * pc p * mpool i p {(cs,I)}) 
          (lr (pcINC cs p) * pc (f p) * mpool i p {(cs,I)})`;


(* ----------------------------------------------------------------------------- *)
(* Some tactics                                                                  *)
(* ----------------------------------------------------------------------------- *)

val IN_PROCESSORS = prove(
  ``(x:('a,'b,'c)processor) IN PROCESSORS ==> 
    ?set n pc i. (x = (set,n,pc,i)) /\ ((!s::set. (n s) IN set))``,
  Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'` \\ SRW_TAC [] [PROCESSORS_def]);

val INIT_TAC =
  ONCE_REWRITE_TAC [RES_FORALL] \\ BETA_TAC
  \\ NTAC 2 STRIP_TAC 
  \\ STRIP_ASSUME_TAC (UNDISCH IN_PROCESSORS)
  \\ ASM_REWRITE_TAC []
  \\ PAT_ASSUM ``x = (set,n,pc,i)`` (fn th => ALL_TAC)
  \\ PAT_ASSUM ``x IN PROCESSORS`` (fn th => ALL_TAC);
    
val IN_PR_EQ = prove(
  ``!set n pc i. (set,n,pc,i) IN PROCESSORS = (!s::set. (n s) IN set)``,
  SRW_TAC [] [PROCESSORS_def]);

fun RES_SPEC t th =
  let
    val th = ONCE_REWRITE_RULE [RES_FORALL] th
    val th = Q.SPEC t th
    val th = DISCH_ALL (CONV_RULE BETA_CONV (UNDISCH th))
    val th = CONV_RULE (RATOR_CONV (REWRITE_CONV [IN_PR_EQ])) th
  in
    th
  end;

val RES_SPEC' = RES_SPEC `(set,n,pc,i)`;


(* ----------------------------------------------------------------------------- *)
(* Properties of pc and set operations                                           *)
(* ----------------------------------------------------------------------------- *)

val pcADD_pcADD = store_thm("pcADD_pcADD",
  ``!k k'. pcADD k o pcADD k' = pcADD (k + k')``,
  SIMP_TAC std_ss [FUN_EQ_THM,pcADD_def,wLENGTH_def,WORD_ADD_ASSOC]);

val pcADD_pcINC = store_thm("pcADD_pcINC",
  ``!k xs:word32 list. pcADD k o pcINC xs = pcADD (k + wLENGTH xs)``,
  REWRITE_TAC [GSYM pcADD_pcADD,pcINC_def]);

val pcINC_pcADD = store_thm("pcINC_pcADD",
  ``!k xs:word32 list. pcINC xs o pcADD k = pcADD (k + wLENGTH xs)``,
  ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ REWRITE_TAC [GSYM pcADD_pcADD,pcINC_def]);

val pcINC_pcINC = store_thm("pcINC_pcINC",
  ``!xs:word32 list ys. pcINC ys o pcINC xs = pcINC (xs++ys)``,
  REWRITE_TAC [pcINC_def,pcADD_pcADD] \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ REWRITE_TAC [wLENGTH_def,word_add_n2w,LENGTH_APPEND]);
  
val pcSET_ABSORB = store_thm("pcSET_ABSORB",
  ``!x f. pcSET x o f = pcSET x``,
  SIMP_TAC std_ss [pcSET_def,FUN_EQ_THM]);

val pcADD_0 = store_thm("pcADD_0",
  ``pcADD 0w = I``,SRW_TAC [] [WORD_ADD_0,pcADD_def,FUN_EQ_THM]);

val pcINC_0 = store_thm("pcINC_0",
  ``pcINC [] = I``,SRW_TAC [] [pcINC_def,wLENGTH_def,LENGTH,pcADD_0]);

val setAPP_CLAUSES = store_thm("setAPP_CLAUSES",
  ``!g Q f Z. (setAPP g {} = {}) /\ 
              (setAPP g ((Q,f) INSERT Z) = (Q,f o g) INSERT setAPP g Z)``,
  REWRITE_TAC [setAPP_def]
  \\ ONCE_REWRITE_TAC [EXTENSION]
  \\ SRW_TAC [] [GSPECIFICATION] 
  THEN1 (Cases_on `x'` \\ SIMP_TAC std_ss [])
  \\ EQ_TAC \\ STRIP_TAC << [
    Cases_on `x'` \\ FULL_SIMP_TAC std_ss [] 
    \\ DISJ2_TAC \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [],
    Q.EXISTS_TAC `(Q,f)` \\ FULL_SIMP_TAC std_ss [],
    Cases_on `x'` \\ FULL_SIMP_TAC std_ss [] 
    \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []]);
        
val setAPP_setAPP = store_thm("setAPP_setAPP",
  ``!f g x. setAPP f (setAPP g x) = setAPP (g o f) x``,
  SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,setAPP_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  \\ Cases_on `x''` \\ FULL_SIMP_TAC std_ss [] << [
    Cases_on `x''` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(q',r')` \\ FULL_SIMP_TAC std_ss [],
    Q.EXISTS_TAC `(q,r o g)` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []]);

val setADD_setADD = store_thm("setADD_setADD",
  ``!k k' x. setADD k (setADD k' x) = setADD (k + k') x``,
  SIMP_TAC std_ss [setADD_def,setAPP_setAPP,pcADD_pcADD]
  \\ REWRITE_TAC [Once WORD_ADD_COMM]);

val setAPP_UNION = store_thm("setAPP_UNION",
  ``!f x y. setAPP f (x UNION y) = setAPP f x UNION setAPP f y``,
  SIMP_TAC std_ss [EXTENSION,GSPECIFICATION,setAPP_def,IN_UNION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  \\ Cases_on `x''` \\ FULL_SIMP_TAC std_ss []   
  THEN1 (DISJ1_TAC \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [])
  THEN1 (DISJ2_TAC \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [])
  \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []);

val setAPP_I = store_thm("setAPP_I",
  ``!x. setAPP I x = x``,
  SIMP_TAC std_ss [setAPP_def,EXTENSION,GSPECIFICATION] 
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  THEN1 (Cases_on `x''` \\ FULL_SIMP_TAC std_ss [])
  \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []);

val setADD_CLAUSES = store_thm("setADD_CLAUSES",
  ``!k Q f Z. (setADD k {} = {}) /\ 
              (setADD k ((Q,f) INSERT Z) = (Q,f o (pcADD k)) INSERT setADD k Z)``,
  REWRITE_TAC [setADD_def,setAPP_CLAUSES]);

val setADD_UNION = store_thm("setADD_UNION",
  ``!k x y. setADD k (x UNION y) = setADD k x UNION setADD k y``,
  REWRITE_TAC [setADD_def,setAPP_UNION]);

val setADD_0 = store_thm("setADD_0",
  ``setADD 0w x = x``,SRW_TAC [] [setADD_def,FUN_EQ_THM,pcADD_0,setAPP_I]);

val setINC_CLAUSES = store_thm("setINC_CLAUSES",
  ``!cs Q f Z. (setINC cs {} = {}) /\ 
               (setINC cs ((Q,f) INSERT Z) = (Q,f o (pcINC cs)) INSERT setINC cs Z)``,
  REWRITE_TAC [setINC_def,setADD_CLAUSES,pcINC_def]);

val setSTAR_CLAUSES = store_thm("setSTAR_CLAUSES",
  ``!P Q f Z. (setSTAR P {} = {}) /\ 
              (setSTAR P ((Q,f) INSERT Z) = (Q * P,f) INSERT setSTAR P Z)``,
  REWRITE_TAC [setSTAR_def]
  \\ ONCE_REWRITE_TAC [EXTENSION]
  \\ SRW_TAC [] [GSPECIFICATION] 
  THEN1 (Cases_on `x'` \\ SIMP_TAC std_ss [])
  \\ EQ_TAC \\ STRIP_TAC << [
    Cases_on `x'` \\ FULL_SIMP_TAC std_ss [] 
    \\ DISJ2_TAC \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [],
    Q.EXISTS_TAC `(Q,f)` \\ FULL_SIMP_TAC std_ss [],
    Cases_on `x'` \\ FULL_SIMP_TAC std_ss [] 
    \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []]);

val IN_setSTAR = store_thm("IN_setSTAR",
  ``!P Q f Z. (Q,f) IN setSTAR P Z = ?Q'. (Q',f) IN Z /\ (Q = Q' * P)``,
  REWRITE_TAC [setSTAR_def] \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [GSPECIFICATION] << [  
    Cases_on `x` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `q` \\ FULL_SIMP_TAC std_ss [],
    Q.EXISTS_TAC `(Q',f)` \\ FULL_SIMP_TAC std_ss []]);
     

(* ----------------------------------------------------------------------------- *)
(* Properties of mset                                                            *)
(* ----------------------------------------------------------------------------- *)

val mset_CASES = store_thm("mset_CASES",
  ``!x xs i a f.
      (mset i a ([],f) = {}) /\ 
      (mset i a (x::xs,f) = i (f a,x) INSERT mset i a (xs,$+ 1w o f))``,
  REPEAT STRIP_TAC << [
    SRW_TAC [] [mset_def,LENGTH,EVAL ``k < 0``,EXTENSION,GSPECIFICATION]
    \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss [],
    ONCE_REWRITE_TAC [EXTENSION]    
    \\ SIMP_TAC std_ss [GSPECIFICATION,mset_def,IN_INSERT] 
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC << [
      Cases_on `x''` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [EL,HD,TL,WORD_ADD_0,LENGTH]
      \\ DISJ2_TAC \\ Q.EXISTS_TAC `(q,n)` 
      \\ FULL_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w] 
      \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM],
      Q.EXISTS_TAC `(x,0)` \\ FULL_SIMP_TAC std_ss [LENGTH,EL,HD,WORD_ADD_0],
      Cases_on `x''` \\ FULL_SIMP_TAC std_ss []
      \\ Q.EXISTS_TAC `(q,SUC r)` 
      \\ FULL_SIMP_TAC std_ss [LENGTH,EL,TL,ADD1,GSYM word_add_n2w]
      \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM]]]);
      

(* ----------------------------------------------------------------------------- *)
(* Properties of mpool                                                           *)
(* ----------------------------------------------------------------------------- *)

val mpool_SING = prove(
  ``!i a xs f. mpool i a {(xs,f)} = BIGSTAR (mset i a (xs,f))``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [mpool_def]
  \\ `{mset i a z | z IN {(xs,f)}} = {mset i a (xs,f)}` by ALL_TAC
  \\ ASM_REWRITE_TAC [BIGUNION_INSERT,BIGUNION_EMPTY,UNION_EMPTY]     
  \\ SRW_TAC [] [Once EXTENSION,GSPECIFICATION]);

val mpool_eq_msequence = store_thm("mpool_eq_msequence",
  ``!xs (f:'b word->'b word) a (i:('b word # 'c)->'a set -> bool). 
       (!a b x y. (i (a,x) = i (b,y)) ==> (a = b) ) /\ 
       (LENGTH xs <= dimword (:'b)) ==> 
       (mpool i a {(xs,f)} = msequence i (f a) xs)``,
  SIMP_TAC bool_ss [RES_FORALL,mpool_SING]
  \\ Induct_on `xs`
  \\ REWRITE_TAC [msequence_def,mset_CASES,BIGSTAR_EMPTY,LENGTH]
  \\ REPEAT STRIP_TAC
  \\ `LENGTH xs < dimword (:'b)` by DECIDE_TAC
  \\ `~(i (f a,h) IN mset i a (xs,$+ 1w o (f:'b word->'b word)))` by ALL_TAC << [
    SIMP_TAC std_ss [mset_def,GSPECIFICATION]
    \\ REPEAT STRIP_TAC
    \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
    \\ `f a = 1w + f a + n2w r` by METIS_TAC []
    \\ `f a = f a + n2w (SUC r)` by METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM,ADD1,word_add_n2w]
    \\ `!x y. (x = x + y) = (y = 0w:'b word)` by METIS_TAC [WORD_ADD_SUB,WORD_ADD_COMM,WORD_EQ_SUB_ZERO]
    \\ `n2w (SUC r) = 0w:'b word` by METIS_TAC []
    \\ `SUC r <= LENGTH xs` by METIS_TAC [LESS_OR]
    \\ `SUC r < dimword (:'b)` by METIS_TAC [LESS_EQ_LESS_TRANS]
    \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword]
    \\ DECIDE_TAC,
    ASM_SIMP_TAC std_ss [BIGSTAR_INSERT]
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (a * x = a * y:'a set -> bool)``)
    \\ `f a + 1w = ($+ 1w o f) a` by (SIMP_TAC std_ss [] \\ METIS_TAC [WORD_ADD_COMM])
    \\ ASM_REWRITE_TAC []
    \\ `LENGTH xs <= dimword (:'b)` by DECIDE_TAC
    \\ METIS_TAC []]);

val pcINC_APPEND = prove(
  ``!cs cs'. pcINC (cs++cs') = pcINC cs' o pcINC cs``, 
  SIMP_TAC std_ss [FUN_EQ_THM,pcINC_def,pcADD_def,wLENGTH_def,LENGTH_APPEND]
  \\ REWRITE_TAC [WORD_ADD_ASSOC,word_add_n2w,Once ADD_COMM]);

val mpool_APP = prove(
  ``!i p k cs. mpool i (f p) cs = mpool i p (setAPP f cs)``,
  SRW_TAC [] [mpool_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] 
                   ``(x=y)==>(BIGSTAR (BIGUNION x) = BIGSTAR (BIGUNION y))``)
  \\ SRW_TAC [] [Once EXTENSION,GSPECIFICATION,setAPP_def]
  \\ EQ_TAC \\ STRIP_TAC << [
    Cases_on `z`
    \\ Q.EXISTS_TAC `(q,r o f)`
    \\ ASM_SIMP_TAC std_ss [mset_def]
    \\ Q.EXISTS_TAC `(q,r)`
    \\ ASM_SIMP_TAC std_ss [],
    Cases_on `x'` 
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(q,r)`
    \\ FULL_SIMP_TAC std_ss [mset_def]]);

val mpool_ADD = prove(
  ``!i p k cs. mpool i (p + k) cs = mpool i p (setADD k cs)``,
  ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ REWRITE_TAC [GSYM (SIMP_CONV bool_ss [pcADD_def] ``pcADD k p``)]
  \\ REWRITE_TAC [mpool_APP,setADD_def]);

val mpool_INC = prove(
  ``!i p cs. mpool i (p + wLENGTH c) cs = mpool i p (setINC c cs)``,
  REWRITE_TAC [mpool_ADD,setINC_def]);

val mset_INSERT = prove(
  ``{mset i p z | z | z IN (c,f) INSERT cs'} = 
    mset i p (c,f) INSERT {mset i p z | z | z IN cs'}``,
  SRW_TAC [] [Once EXTENSION]
  \\ EQ_TAC \\ STRIP_TAC
  \\ METIS_TAC []);

val mpool_EMPTY_INSERT = prove(
  ``!(i:'b word # 'c->'a set->bool) p C f. mpool i p (([],f) INSERT C) = mpool i p C``,
  REWRITE_TAC [mpool_def]
  \\ REWRITE_TAC [mset_INSERT,IN_INSERT,NOT_IN_EMPTY]
  \\ REPEAT STRIP_TAC
  \\ `mset i p ([],f) = {}` by ALL_TAC << [
    SRW_TAC [] [mset_def,EXTENSION,GSPECIFICATION] 
    \\ Cases_on `x'` \\ ASM_SIMP_TAC std_ss [],
    ONCE_REWRITE_TAC [INSERT_SING_UNION]
    \\ `BIGUNION {({}:'a set set set)} = {}` by SRW_TAC [] [BIGUNION,EXTENSION]
    \\ ASM_SIMP_TAC std_ss [BIGUNION_UNION,UNION_EMPTY]]);  
    
val mpool_EXTEND = prove(
  ``!i p cs cs'. ?X. mpool i p cs * X = mpool i p (cs UNION cs')``,
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [mpool_def] 
  \\ MATCH_MP_TAC (GSYM BIGSTAR_EXTEND)
  \\ SRW_TAC [] [SUBSET_DEF,BIGUNION,GSPECIFICATION]
  \\ Q.EXISTS_TAC `mset i p z` 
  \\ ASM_REWRITE_TAC []
  \\ Q.EXISTS_TAC `z`
  \\ ASM_REWRITE_TAC []);

val mpool_EXTEND_INSERT = prove(
  ``?X. mpool i p cs * X = mpool i p ((d,f) INSERT cs)``,
  METIS_TAC [INSERT_SING_UNION,UNION_COMM,mpool_EXTEND]);

val LENGTH_LESS_EQ = prove(
  ``!c c'. LENGTH c <= LENGTH (c++c')``,
  Induct \\ SRW_TAC [] [LENGTH]);

val LENGTH_LESS_APPEND = prove(
  ``!r c c'. r < LENGTH c ==> r < LENGTH (c++c')``,
  SRW_TAC [] [LENGTH_LESS_EQ] \\ DECIDE_TAC)

val LENGTH_LESS_APPEND2 = prove(
  ``!r c c'. r < LENGTH c ==> r < LENGTH (c'++c)``,
  SRW_TAC [] [LENGTH_LESS_EQ] \\ DECIDE_TAC)

val EL_EQ_EL_APPEND = prove(
  ``!r c c'. r < LENGTH c ==> (EL r c = EL r (c++c'))``,
  Induct << [
    REPEAT STRIP_TAC    
    \\ Cases_on `c`
    \\ FULL_SIMP_TAC std_ss [LENGTH,EL,APPEND,HD],
    SIMP_TAC bool_ss [LENGTH,EL,APPEND]
    \\ REPEAT STRIP_TAC
    \\ Cases_on `c`
    \\ FULL_SIMP_TAC std_ss [LENGTH,EL,APPEND,HD,TL]]);

val EL_APPEND = prove(
  ``!c c' k. EL (LENGTH c + k) (c ++ c') = EL k c'``,
  Induct \\ ASM_SIMP_TAC bool_ss [LENGTH,ADD,EL,APPEND,TL]);

val EL_EQ_EL_APPEND2 = prove(
  ``!r c c'. r < LENGTH c' ==> (EL r c' = EL (LENGTH c + r) (c++c'))``,
  Induct
  \\ SIMP_TAC bool_ss [LENGTH,EL,APPEND]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `c'`
  \\ FULL_SIMP_TAC std_ss [LENGTH,EL,APPEND,HD,TL,EL_APPEND]);

val EL_APPEND_FRONT = prove(      
  ``!r c c'. r < LENGTH c ==> (EL r (c++c') = EL r c)``,
  Induct  
  \\ REPEAT STRIP_TAC    
  \\ Cases_on `c`
  \\ FULL_SIMP_TAC std_ss [LENGTH,EL,APPEND,HD,TL,EL_APPEND]);

val EL_APPEND_TAIL = prove(      
  ``!r c c'. ~(r < LENGTH c) /\ r < LENGTH (c++c') ==> (EL r (c++c') = EL (r-LENGTH c) c')``,
  Induct  
  \\ REPEAT STRIP_TAC    
  \\ Cases_on `c`
  \\ FULL_SIMP_TAC std_ss [LENGTH,EL,APPEND,HD,TL,EL_APPEND]);

val mpool_MERGE_LEMMA = prove(
  ``BIGUNION {mset i p (c',f); mset i p (c'',pcINC c' o f)} =
    BIGUNION {mset i p (c' ++ c'',f)}``,
  SRW_TAC [] [BIGUNION,Once EXTENSION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [mset_def,GSPECIFICATION]
  \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss [] << [    
    Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []
    \\ METIS_TAC [EL_EQ_EL_APPEND,LENGTH_LESS_APPEND],   
    Q.EXISTS_TAC `(q,LENGTH c' + r)` \\ FULL_SIMP_TAC std_ss []     
    \\ ASM_SIMP_TAC std_ss [pcINC_def,pcADD_def,GSYM word_add_n2w,GSYM wLENGTH_def]
    \\ STRIP_TAC THEN1 (METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM])
    \\ REWRITE_TAC [LENGTH_APPEND] \\ STRIP_TAC THEN1 DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [EL_EQ_EL_APPEND2], 
    Cases_on `r < LENGTH c'` << [
      Q.EXISTS_TAC `mset i p (c',f)` 
      \\ SRW_TAC [] [mset_def,GSPECIFICATION]     
      \\ Q.EXISTS_TAC `(EL r c',r)` \\ FULL_SIMP_TAC std_ss []
      \\ METIS_TAC [EL_EQ_EL_APPEND],
      Q.EXISTS_TAC `mset i p (c'',pcINC c' o f)` 
      \\ SRW_TAC [] [mset_def,GSPECIFICATION]     
      \\ Q.EXISTS_TAC `(EL (r-LENGTH c') c'',r-LENGTH c')` 
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
      \\ `0 < LENGTH c''` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [pcINC_def,pcADD_def]
      \\ `LENGTH c' <= r` by DECIDE_TAC
      \\ `wLENGTH c' + f p + n2w (r - LENGTH c') = f p + n2w r`
                by METIS_TAC [WORD_ADD_COMM,WORD_ADD_ASSOC,word_add_n2w,wLENGTH_def,SUB_ADD]
      \\ FULL_SIMP_TAC std_ss [EL_APPEND_TAIL,LENGTH_APPEND]]]);

val mpool_MERGE = prove(
  ``mpool i p ((c',f) INSERT (c'',pcINC c' o f) INSERT C) =
    mpool i p ((c'++c'',f) INSERT C)``,
  REWRITE_TAC [mpool_def,mset_INSERT]
  \\ ONCE_REWRITE_TAC [INSERT_SING_UNION]
  \\ ONCE_REWRITE_TAC [INSERT_SING_UNION]
  \\ REWRITE_TAC [UNION_ASSOC] 
  \\ ONCE_REWRITE_TAC [BIGUNION_UNION]
  \\ REWRITE_TAC [UNION_EMPTY,GSYM INSERT_SING_UNION,mpool_MERGE_LEMMA]);


(* ----------------------------------------------------------------------------- *)
(* Properties of run                                                             *)
(* ----------------------------------------------------------------------------- *)

val run_IN_set = prove(
  ``(!s::set. next s IN set) ==> (!k. !s::set. run next (k,s) IN set)``,
  STRIP_TAC \\ Induct \\ SRW_TAC [] [run_def]);

val run_SWITCH = prove(
  ``!k n s. run n (k,n s) = n (run n (k,s))``,
  Induct \\ SRW_TAC [] [run_def]);

val run_ADD = prove(
  ``!s n k k'. run n (k,run n (k',s)) = run n (k+k',s)``,
  Induct_on `k` \\ SRW_TAC [] [run_def,ADD,run_SWITCH]);
  

(* ----------------------------------------------------------------------------- *)
(* Theorems for RUN                                                              *)
(* ----------------------------------------------------------------------------- *)

val RUN_FRAME = store_thm("RUN_FRAME",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P Q. RUN x P Q ==> !R. RUN x (P * R) (Q * R)``,
  INIT_TAC \\ SRW_TAC [] [RUN_def,GSYM STAR_ASSOC]);    

val RUN_STRENGTHEN_PRE = store_thm("RUN_STRENGTHEN_PRE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P P' Q. SEP_IMP P' P /\ RUN x P Q ==> RUN x P' Q``,
  INIT_TAC \\ SRW_TAC [] [RUN_def] 
  \\ METIS_TAC [SEP_IMP_FRAME,SEP_IMP_def]);

val RUN_WEAKEN_POST = store_thm("RUN_WEAKEN_POST",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P Q Q'. SEP_IMP Q Q' /\ RUN x P Q ==> RUN x P Q'``,
  INIT_TAC \\ SRW_TAC [] [RUN_def] 
  \\ METIS_TAC [SEP_IMP_FRAME,SEP_IMP_def]);

val RUN_COMPOSE = store_thm("RUN_COMPOSE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P P' M Q Q'. RUN x P (Q \/ M) /\ RUN x (M \/ P') Q' ==> RUN x (P \/ P') (Q \/ Q')``,
  INIT_TAC \\ SRW_TAC [] [RUN_def,GSYM STAR_OVER_DISJ]
  \\ FULL_SIMP_TAC std_ss [SEP_DISJ_def] 
  \\ METIS_TAC [run_ADD,run_IN_set]);

val RUN_HIDE_PRE = store_thm("RUN_HIDE_PRE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P P' Q. (!y:'var. RUN x (P * P' y) Q) = RUN x (P * ~ P') Q``,
  INIT_TAC \\ REPEAT STRIP_TAC   
  \\ SIMP_TAC bool_ss [RUN_def,RES_FORALL,SEP_HIDE_def]
  \\ EQ_TAC \\ REPEAT STRIP_TAC << [  
    `!y. (P * P' y * R) s ==> ?k. (Q * R) (run n (k,s))` by METIS_TAC []
    \\ FULL_MOVE_STAR_TAC `x*y*z` `(x*z)*y`
    \\ Q.ABBREV_TAC `X = P * R`
    \\ Q.ABBREV_TAC `Y = Q * R`
    \\ Q.PAT_ASSUM `!x y. b` (fn th => ALL_TAC)
    \\ NTAC 2 (Q.PAT_ASSUM `Abbrev b` (fn th => ALL_TAC))
    \\ CCONTR_TAC    
    \\ FULL_SIMP_TAC bool_ss [STAR_def]
    \\ METIS_TAC [],
    `(P * (\s. ?x. P' x s) * R) s ==> ?k. (Q * R) (run n (k,s))` by METIS_TAC []
    \\ Q.PAT_ASSUM `!x. b ==> !r. c` (fn th => ALL_TAC)
    \\ FULL_MOVE_STAR_TAC `x*y*z` `(x*z)*y` 
    \\ Q.ABBREV_TAC `X = P * R`
    \\ Q.ABBREV_TAC `Y = Q * R`
    \\ NTAC 2 (Q.PAT_ASSUM `Abbrev b` (fn th => ALL_TAC))
    \\ CCONTR_TAC    
    \\ FULL_SIMP_TAC bool_ss [STAR_def]
    \\ METIS_TAC []]);

val RUN_HIDE_POST = store_thm("RUN_HIDE_POST",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P Q Q' y:'var. RUN x P (Q * Q' y) ==> RUN x P (Q * ~ Q')``,
  METIS_TAC [RUN_WEAKEN_POST,SEP_HIDE_INTRO]);

val RUN_LOOP = store_thm("RUN_LOOP",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !Inv P Q.
        (?R. WF R /\ 
           !v:'var. RUN x (Inv v \/ P) (Q \/ SEP_EXISTS v'. Inv v' * cond (R v' v))) ==>
        (!v:'var. RUN x (Inv v \/ P) Q)``,
  INIT_TAC 
  \\ NTAC 4 STRIP_TAC
  \\ recInduct (UNDISCH (SPEC_ALL relationTheory.WF_INDUCTION_THM))
  \\ FULL_SIMP_TAC std_ss [RUN_def,GSYM STAR_OVER_DISJ,RES_FORALL]
  \\ FULL_SIMP_TAC std_ss [SEP_EXISTS_ABSORB_STAR,SEP_EXISTS_THM]
  \\ REPEAT STRIP_TAC
  \\ PAT_ASSUM ``!v:'a s:'b. b`` 
       (STRIP_ASSUME_TAC o SIMP_RULE std_ss [SEP_DISJ_def,SEP_EXISTS_THM] o 
        UNDISCH o SPEC_ALL o UNDISCH o Q.SPECL [`x`,`s`])
  THEN1 (Q.EXISTS_TAC `k` \\ ASM_REWRITE_TAC [])
  \\ ASM_MOVE_STAR_TAC `x*cond c*y` `cond c*(x*y)`
  \\ FULL_SIMP_TAC std_ss [cond_STAR]  
  \\ `run n (k,s) IN set` by METIS_TAC [run_IN_set]
  \\ `(Inv v' * R' \/ P * R') (run n (k,s))` by METIS_TAC [SEP_DISJ_def]
  \\ PAT_ASSUM ``!y:'a. R y x ==> b`` 
       (STRIP_ASSUME_TAC o UNDISCH o Q.SPEC `R'` o UNDISCH o 
        Q.SPEC `run n (k,s)` o UNDISCH o Q.SPEC `v'`)
  \\ Q.EXISTS_TAC `k' + k`
  \\ FULL_SIMP_TAC std_ss [run_ADD]);

val RUN_FRAME' = RES_SPEC' RUN_FRAME;
val RUN_STRENGTHEN_PRE' = RES_SPEC' RUN_STRENGTHEN_PRE;
val RUN_WEAKEN_POST' = RES_SPEC' RUN_WEAKEN_POST;
val RUN_COMPOSE' = RES_SPEC' RUN_COMPOSE;
val RUN_HIDE_PRE' = RES_SPEC' RUN_HIDE_PRE;
val RUN_HIDE_POST' = RES_SPEC' RUN_HIDE_POST;
val RUN_LOOP' = RES_SPEC' RUN_LOOP;


(* ----------------------------------------------------------------------------- *)
(* Theorems for GPROG                                                            *)
(* ----------------------------------------------------------------------------- *)

val BIGD_FRAME = prove(
  ``!R Y. 
      SEP_BIGDISJ {P * mpool i p C * pc (f p) * R | (P,f) | (P,f) IN Y} =
      SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN Y} * R``,
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [STAR_OVER_BIGDISJ]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ ONCE_REWRITE_TAC [EXTENSION]
  \\ SIMP_TAC bool_ss [GSPECIFICATION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss [] << [
    Q.EXISTS_TAC `q * mpool i p C * pc (r p)`
    \\ STRIP_TAC THEN1 SIMP_TAC (std_ss++star_ss) []
    \\ Q.EXISTS_TAC `(q,r)` \\ ASM_SIMP_TAC std_ss [],
    Q.EXISTS_TAC `(q,r)` \\ ASM_SIMP_TAC std_ss []]);

val BIGD_UNION = prove(
  ``!Y Z. 
      SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN Y UNION Z} =
      SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN Y} \/
      SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN Z}``,
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [GSYM SEP_BIGDISJ_CLAUSES]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ ONCE_REWRITE_TAC [EXTENSION]
  \\ SIMP_TAC std_ss [GSPECIFICATION,IN_UNION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss [] << [
    DISJ1_TAC \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [],
    DISJ2_TAC \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [],
    Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [], 
    Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []]);

val BIGD_INSERT = prove(
  ``!Q g Z. 
      SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN (Q,g) INSERT Z} =
      Q * mpool i p C * pc (g p) \/ 
      SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN Z}``,
  REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [INSERT_SING_UNION]
  \\ REWRITE_TAC [BIGD_UNION]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (x \/ z = y \/ (z:'a set -> bool))``)
  \\ `{P*mpool i p C * pc (f p) |(P,f)| (P,f) IN {(Q,g)}} = {Q*mpool i p C*pc (g p)}` by ALL_TAC
  \\ ASM_REWRITE_TAC [SEP_BIGDISJ_CLAUSES,SEP_DISJ_CLAUSES]
  \\ ONCE_REWRITE_TAC [EXTENSION]
  \\ SIMP_TAC std_ss [GSPECIFICATION,IN_UNION,IN_INSERT,NOT_IN_EMPTY]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  THEN1 (Cases_on `x'` \\ FULL_SIMP_TAC std_ss [])
  \\ Q.EXISTS_TAC `(Q,g)` \\ FULL_SIMP_TAC std_ss []);

val BIGD_EMPTY = prove(
  ``SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN {}} = SEP_F``,
  REWRITE_TAC [GSYM SEP_BIGDISJ_CLAUSES]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ SRW_TAC [] [EXTENSION,GSPECIFICATION]  
  \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss []);


val GPROG_FRAME_LEMMA = prove(
  ``!R Y. 
      SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN setSTAR R Y} =
      SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN Y} * R``,
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [GSYM BIGD_FRAME,IN_setSTAR]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ ONCE_REWRITE_TAC [EXTENSION]
  \\ SIMP_TAC std_ss [GSPECIFICATION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC 
  \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
  THEN1 (Q.EXISTS_TAC `(Q',r)` \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  \\ Q.EXISTS_TAC `(q * R,r)` \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ Q.EXISTS_TAC `q` \\ FULL_SIMP_TAC (std_ss++star_ss) []);
          
val GPROG_FRAME = store_thm("GPROG_FRAME",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !Y C Z. 
        GPROG x Y C Z ==> !R. GPROG x (setSTAR R Y) C (setSTAR R Z)``,
  INIT_TAC \\ ASM_SIMP_TAC std_ss [RUN_FRAME',GPROG_def,GPROG_FRAME_LEMMA]);
    
val GPROG_ADD_CODE = store_thm("GPROG_ADD_CODE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !Y C Z. GPROG x Y C Z ==> !C'. GPROG x Y (C UNION C') Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def] \\ REPEAT STRIP_TAC 
  \\ `?X. mpool i p (C UNION C') = mpool i p C * X` by METIS_TAC [mpool_EXTEND]
  \\ ASM_REWRITE_TAC [] \\ MOVE_STAR_TAC `x*(y*z)*q` `(x*y*q)*z` 
  \\ ASM_SIMP_TAC std_ss [BIGD_FRAME,RUN_FRAME']);

val GPROG_STRENGTHEN_PRE = store_thm("GPROG_STRENGTHEN_PRE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P P' Y C Z f.
        SEP_IMP P' P /\ GPROG x ((P,f) INSERT Y) C Z ==> GPROG x ((P',f) INSERT Y) C Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,BIGD_INSERT,GSYM STAR_ASSOC] \\ REPEAT STRIP_TAC
  \\ PAT_ASSUM ``!p:'a. b`` (ASSUME_TAC o SPEC_ALL)
  \\ `!R X. SEP_IMP (P' * R \/ X)  (P * R \/ X)` by METIS_TAC [SEP_IMP_FRAME,SEP_IMP_MONO_DISJ]
  \\ MATCH_MP_TAC (UNDISCH RUN_STRENGTHEN_PRE')
  \\ METIS_TAC []);

val GPROG_DELETE_PRE = store_thm("GPROG_DELETE_PRE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !Y Y' C Z. GPROG x (Y UNION Y') C Z ==> GPROG x Y C Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,BIGD_UNION] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (UNDISCH RUN_STRENGTHEN_PRE')
  \\ PAT_ASSUM ``!p:'a.b`` (ASSUME_TAC o SPEC_ALL)
  \\ Q.ABBREV_TAC `X1 = SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN Y}`
  \\ Q.ABBREV_TAC `X2 = SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN Y'}`
  \\ Q.EXISTS_TAC `X1 \/ X2` \\ ASM_REWRITE_TAC []
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def]);

val GPROG_WEAKEN_POST = store_thm("GPROG_WEAKEN_POST",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !Y C Q Q' Z f.
        SEP_IMP Q Q' /\ GPROG x Y C ((Q,f) INSERT Z) ==> GPROG x Y C ((Q',f) INSERT Z)``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,BIGD_INSERT,GSYM STAR_ASSOC] \\ REPEAT STRIP_TAC
  \\ PAT_ASSUM ``!p:'a. b`` (ASSUME_TAC o SPEC_ALL)
  \\ `!R X. SEP_IMP (Q * R \/ X)  (Q' * R \/ X)` by METIS_TAC [SEP_IMP_FRAME,SEP_IMP_MONO_DISJ]
  \\ MATCH_MP_TAC (UNDISCH RUN_WEAKEN_POST')
  \\ METIS_TAC []);

val GPROG_ADD_POST = store_thm("GPROG_ADD_POST",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !Y C Z. GPROG x Y C Z ==> !Z'. GPROG x Y C (Z UNION Z')``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,BIGD_UNION] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (UNDISCH RUN_WEAKEN_POST')
  \\ PAT_ASSUM ``!p:'a.b`` (ASSUME_TAC o SPEC_ALL)
  \\ Q.ABBREV_TAC `X1 = SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN Z}`
  \\ Q.ABBREV_TAC `X2 = SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN Z'}`
  \\ Q.EXISTS_TAC `X1` \\ ASM_REWRITE_TAC []
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def]);

val GPROG_FALSE_PRE = store_thm("GPROG_FALSE_PRE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !f Y C Z. GPROG x ((SEP_F,f) INSERT Y) C Z = GPROG x Y C Z``,
  INIT_TAC \\ SIMP_TAC std_ss [GPROG_def,BIGD_INSERT,F_STAR,SEP_DISJ_CLAUSES]);

val GPROG_FALSE_POST = store_thm("GPROG_FALSE_POST",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !f Y C Z. GPROG x Y C ((SEP_F,f) INSERT Z) = GPROG x Y C Z``,
  INIT_TAC \\ SIMP_TAC std_ss [GPROG_def,BIGD_INSERT,F_STAR,SEP_DISJ_CLAUSES]);

val GPROG_EMPTY_CODE = store_thm("GPROG_EMPTY_CODE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !f Y C Z.
        GPROG x Y (([],f) INSERT C) Z = GPROG x Y C Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,mpool_EMPTY_INSERT]);

val GPROG_SHIFT_LEMMA = prove(
  ``!g Y. 
      SEP_BIGDISJ {P * mpool i (g p) C * pc (f p) |(P,f)| (P,f) IN setAPP g Y} =
      SEP_BIGDISJ {P * mpool i (g p) C * pc (f (g p)) |(P,f)| (P,f) IN Y}``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [setAPP_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``) 
  \\ ONCE_REWRITE_TAC [EXTENSION]
  \\ SIMP_TAC std_ss [GSPECIFICATION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss [] << [
    Cases_on `x'` \\ FULL_SIMP_TAC std_ss []  
    \\ Q.EXISTS_TAC `(q',r')` \\ FULL_SIMP_TAC std_ss [], 
    Q.EXISTS_TAC `(q,r o g)` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []]);
    
val GPROG_SHIFT = store_thm("GPROG_SHIFT",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !Y C Z. GPROG x Y C Z ==> !g. GPROG x (setAPP g Y) (setAPP g C) (setAPP g Z)``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GSYM mpool_APP] \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [GPROG_SHIFT_LEMMA]);

val GPROG_MERGE_CODE = store_thm("GPROG_MERGE_CODE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !cs cs' f Y C Z. 
        GPROG x Y ((cs,f) INSERT (cs',pcINC cs o f) INSERT C) Z  =
        GPROG x Y ((cs++cs',f) INSERT C) Z ``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,mpool_MERGE,UNION_ASSOC]);

val GPROG_MERGE_PRE = store_thm("GPROG_MERGE_PRE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P P' f Y C Z.
        GPROG x ((P,f) INSERT (P',f) INSERT Y) C Z = 
        GPROG x ((P \/ P',f) INSERT Y) C Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,BIGD_INSERT,SEP_DISJ_ASSOC,STAR_OVER_DISJ]);

val GPROG_MERGE_POST = store_thm("GPROG_MERGE_POST",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !Q Q' f Y C Z.
        GPROG x Y C ((Q,f) INSERT (Q',f) INSERT Z) = 
        GPROG x Y C ((Q \/ Q',f) INSERT Z)``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,BIGD_INSERT,SEP_DISJ_ASSOC,STAR_OVER_DISJ]);

val GPROG_COMPOSE = store_thm("GPROG_COMPOSE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !Y Y' X C C' Z Z'. 
         GPROG x Y C (Z UNION X) /\ GPROG x (X UNION Y') C' Z' ==> 
         GPROG x (Y UNION Y') (C UNION C') (Z UNION Z')``,
  INIT_TAC \\ REPEAT STRIP_TAC 
  \\ `GPROG (set,n,pc,i) Y (C UNION C') (Z UNION X)` by METIS_TAC [RES_SPEC' GPROG_ADD_CODE]
  \\ `GPROG (set,n,pc,i) (X UNION Y') (C UNION C') Z'` 
         by METIS_TAC [RES_SPEC' GPROG_ADD_CODE, UNION_COMM]
  \\ FULL_SIMP_TAC std_ss [GPROG_def,BIGD_UNION]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (UNDISCH RUN_COMPOSE')
  \\ METIS_TAC []);

val GPROG_SET_PC = store_thm("GPROG_SET_PC",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !Y C Z.
        (!p. GPROG x (setAPP (\x.p) Y) (setAPP (\x.p) C) (setAPP (\x.p) Z)) =
        GPROG x Y C Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GSYM mpool_APP] \\ REPEAT STRIP_TAC
  \\ `!Y p:'b word p':'b word. 
        {P * mpool i p C * pc (f p') |(P,f)|(P,f) IN setAPP (\x. p) Y} = 
        {P * mpool i p C * pc (f p)  |(P,f)|(P,f) IN Y}` by ALL_TAC
  \\ ASM_REWRITE_TAC []
  \\ ONCE_REWRITE_TAC [EXTENSION]
  \\ SIMP_TAC std_ss [setAPP_def,GSPECIFICATION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC << [   
    Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(q',r')` \\ FULL_SIMP_TAC std_ss [],
    Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(q,r o (\x.p))` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []]);

val PRE_EXISTS_LEMMA_LEMMA = prove(
  ``!P g. (SEP_EXISTS v. P v * cond (g v)) = SEP_BIGDISJ { P v |v| g v }``,
  ONCE_REWRITE_TAC [(GSYM o BETA_CONV) ``(\b. P b * cond (g b)) b``]
  \\ REWRITE_TAC [SEP_BIGDISJ_CLAUSES,FUN_EQ_THM,SEP_DISJ_CLAUSES,SEP_EXISTS_THM]
  \\ SIMP_TAC std_ss [SEP_BIGDISJ_def,GSPECIFICATION,cond_STAR]  
  \\ METIS_TAC []);

val PRE_EXISTS_LEMMA = prove(
  ``(SEP_EXISTS y. P y * cond (g y)) * mpool i p C * pc (f p) =
    SEP_BIGDISJ 
      {P' * mpool i p C * pc (f' p) |(P',f')|(P',f') IN {(P y,f)|y|g y}}``,
  ONCE_REWRITE_TAC [(GSYM o BETA_CONV) ``(\y. P y * cond (g y)) y``]
  \\ REWRITE_TAC [GSYM STAR_ASSOC]
  \\ REWRITE_TAC [SEP_EXISTS_ABSORB_STAR]
  \\ SIMP_TAC std_ss [STAR_ASSOC]
  \\ MOVE_STAR_TAC `p*c*m*pp` `p*m*pp*c`
  \\ ONCE_REWRITE_TAC 
       [(GSYM o BETA_CONV) ``(\v. P v * mpool i p C * pc (f p)) v``] 
  \\ REWRITE_TAC [PRE_EXISTS_LEMMA_LEMMA]
  \\ SIMP_TAC std_ss []
  \\ `!P' f'. (P',f') IN {(P y,f) | y | g y} = ?y. g y /\ (P' = P y) /\ (f' = f)` 
          by (SRW_TAC [] [GSPECIFICATION] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC []
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ ONCE_REWRITE_TAC [EXTENSION] \\ SRW_TAC [] [GSPECIFICATION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC << [
    Q.EXISTS_TAC `(P v,f)` \\ FULL_SIMP_TAC std_ss [] 
    \\ Q.EXISTS_TAC `v` \\ FULL_SIMP_TAC std_ss [],
    Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `y` \\ FULL_SIMP_TAC std_ss []]);

val GPROG_PRE_EXISTS = store_thm("GPROG_PRE_EXISTS",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P g f Y C Z .
        GPROG x (((SEP_EXISTS y. P y * cond (g y)),f) INSERT Z) C Z =
        GPROG x ({(P y,f) |y| g y } UNION Z) C Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,BIGD_UNION,BIGD_INSERT,BIGD_EMPTY,PRE_EXISTS_LEMMA]);

val GPROG_POST_EXISTS = store_thm("GPROG_POST_EXISTS",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P g f Y C Z .
        GPROG x Y C (((SEP_EXISTS y. P y * cond (g y)),f) INSERT Z) =
        GPROG x Y C ({(P y,f) |y| g y } UNION Z)``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,BIGD_UNION,BIGD_INSERT,BIGD_EMPTY,PRE_EXISTS_LEMMA]);

val GPROG_LOOP = store_thm("GPROG_LOOP",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !Inv Y C Z.
        (?R. WF R /\ 
           !v:'var. GPROG x (Inv v UNION Y) C (Z UNION {i|(i,v')|i IN Inv v' /\ R v' v })) ==>
        (!v:'var. GPROG x (Inv v UNION Y) C Z)``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,BIGD_UNION]
  \\ ONCE_REWRITE_TAC 
      [(GSYM o BETA_CONV) 
       ``(\v. SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN Inv v}) v``]
  \\ REPEAT STRIP_TAC  
  \\ MATCH_MP_TAC (UNDISCH RUN_LOOP')
  \\ Q.EXISTS_TAC `R` \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (UNDISCH RUN_WEAKEN_POST')
  \\ Q.EXISTS_TAC 
       `SEP_BIGDISJ {P * mpool i p C * pc (f p) | (P,f) | (P,f) IN Z} \/
        SEP_BIGDISJ {P*mpool i p C * pc (f p) |(P,f)|(P,f) IN {i|(i,v')|i IN Inv v' /\ R v' v}}`
  \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [SEP_DISJ_SYM]
  \\ MATCH_MP_TAC SEP_IMP_MONO_DISJ
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,SEP_BIGDISJ_def,GSPECIFICATION,cond_STAR]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `r'` \\ ASM_REWRITE_TAC [] 
  \\ Q.EXISTS_TAC `P` \\ ASM_REWRITE_TAC []
  \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []);

val GPROG_LOOP1 = store_thm("GPROG_LOOP1",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !f Inv Y C Z.
        (?R. WF R /\ 
           !v:'var. GPROG x ((Inv v,f) INSERT Y) C
                           (((SEP_EXISTS v'. Inv v' * cond(R v' v)),f) INSERT Z)) ==>
        (!v:'var. GPROG x ((Inv v,f) INSERT Y) C Z)``,
  INIT_TAC \\ NTAC 5 STRIP_TAC
  \\ ONCE_REWRITE_TAC [(GSYM o BETA_CONV) ``(\v. cond (R v' v)) v``]
  \\ ASM_SIMP_TAC bool_ss [UNDISCH (RES_SPEC' GPROG_POST_EXISTS)]
  \\ ONCE_REWRITE_TAC [UNION_COMM]
  \\ `!R:'var->'var->bool v:'var. 
        {(Inv v',f) | v' | R v' v} = {i|(i,v')| i IN {(Inv v',f)} /\ R v' v}` by   
    (SRW_TAC [] [EXTENSION,GSPECIFICATION] \\ EQ_TAC \\ STRIP_TAC    
     THEN1 (Q.EXISTS_TAC `(x,v')` \\ FULL_SIMP_TAC std_ss [])
     \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
     \\ Q.EXISTS_TAC `r` \\ FULL_SIMP_TAC std_ss [])
  \\ ONCE_REWRITE_TAC [INSERT_SING_UNION]
  \\ ASM_SIMP_TAC std_ss [] 
  \\ ONCE_REWRITE_TAC [(GSYM o BETA_CONV) ``(\v. {(Inv v,f)}) v``]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (UNDISCH (RES_SPEC' GPROG_LOOP))
  \\ Q.EXISTS_TAC `R` \\ ASM_REWRITE_TAC []);

val GPROG_FRAME' = RES_SPEC' GPROG_FRAME;
val GPROG_MERGE_PRE' = RES_SPEC' GPROG_MERGE_PRE;
val GPROG_MERGE_POST' = RES_SPEC' GPROG_MERGE_POST;
val GPROG_STRENGTHEN_PRE' = RES_SPEC' GPROG_STRENGTHEN_PRE;
val GPROG_WEAKEN_POST' = RES_SPEC' GPROG_WEAKEN_POST;
val GPROG_FALSE_PRE' = RES_SPEC' GPROG_FALSE_PRE;
val GPROG_FALSE_POST' = RES_SPEC' GPROG_FALSE_POST;
val GPROG_EMPTY_CODE' = RES_SPEC' GPROG_EMPTY_CODE;
val GPROG_ADD_CODE' = RES_SPEC' GPROG_ADD_CODE;
val GPROG_MERGE_CODE' = RES_SPEC' GPROG_MERGE_CODE;
val GPROG_SHIFT' = RES_SPEC' GPROG_SHIFT;
val GPROG_COMPOSE' = RES_SPEC' GPROG_COMPOSE;
val GPROG_LOOP' = RES_SPEC' GPROG_LOOP;
val GPROG_LOOP1' = RES_SPEC' GPROG_LOOP1;


(* ----------------------------------------------------------------------------- *)
(* Theorems for PROG                                                             *)
(* ----------------------------------------------------------------------------- *)

val PROG_FRAME = store_thm("PROG_FRAME",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P cs C Q Z. 
        PROG x P cs C Q Z ==> !R. PROG x (P * R) cs C (Q * R) (setSTAR R Z)``,
  INIT_TAC \\ REWRITE_TAC [PROG_def] \\ REPEAT STRIP_TAC
  \\ `{(P * R,I:'b word->'b word)} = setSTAR R {(P,I)}` by REWRITE_TAC [setSTAR_CLAUSES]
  \\ `(Q * R,pcINC cs) INSERT setSTAR R Z = setSTAR R ((Q,pcINC cs) INSERT Z)` 
         by REWRITE_TAC [setSTAR_CLAUSES]
  \\ ASM_SIMP_TAC std_ss []  
  \\ MATCH_MP_TAC (UNDISCH GPROG_FRAME')
  \\ ASM_REWRITE_TAC []);

val PROG_MERGE = store_thm("PROG_MERGE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P P' cs C C' Q Q' Z Z'. 
        PROG x P cs C Q Z /\ PROG x P' cs C' Q' Z' ==>
        PROG x (P \/ P') cs (C UNION C') (Q \/ Q') (Z UNION Z')``,
  INIT_TAC \\ REWRITE_TAC [PROG_def] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [GSYM (UNDISCH GPROG_MERGE_PRE')]
  \\ ASM_SIMP_TAC std_ss [GSYM (UNDISCH GPROG_MERGE_POST')]
  \\ `!X Y. (Q,pcINC cs) INSERT (Q',pcINC cs) INSERT X UNION Y = 
            ((Q,pcINC cs) INSERT X) UNION ((Q',pcINC cs) INSERT Y)` by 
         SRW_TAC [] [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY,AC (DISJ_COMM) (DISJ_ASSOC)]
  \\ `(cs,I) INSERT C UNION C' = ((cs,I) INSERT C) UNION ((cs,I) INSERT C')` by
         SRW_TAC [] [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY,AC (DISJ_COMM) (DISJ_ASSOC)]
  \\ `{(P,I); (P',I)} = {(P,I)} UNION {(P',I:'b word->'b word)}` by
         SRW_TAC [] [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY,AC (DISJ_COMM) (DISJ_ASSOC)]
  \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC 
        ((REWRITE_RULE [UNION_EMPTY] o Q.INST [`X`|->`{}`] o SPEC_ALL o UNDISCH) GPROG_COMPOSE')
  \\ ASM_REWRITE_TAC []);

val PROG_ABSORB_POST = store_thm("PROG_ABSORB_POST",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P cs C Q Q' Z. 
        PROG x P cs C Q ((Q',pcINC cs) INSERT Z) = PROG x P cs C (Q \/ Q') Z``,
  INIT_TAC \\ ASM_SIMP_TAC std_ss [PROG_def,UNDISCH (GPROG_MERGE_POST')]);

val PROG_MERGE_POST = store_thm("PROG_MERGE_POST",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P cs C Q f Q' Q'' Z. 
        PROG x P cs C Q ((Q',f) INSERT (Q'',f) INSERT Z) = 
        PROG x P cs C Q ((Q' \/ Q'',f) INSERT Z)``,
  INIT_TAC \\ REWRITE_TAC [PROG_def] 
  \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ ASM_SIMP_TAC std_ss [GSYM (UNDISCH (GPROG_MERGE_POST'))]
  \\ METIS_TAC [INSERT_COMM]);

val PROG_FALSE_POST = store_thm("PROG_FALSE_POST",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P cs C f Q Z. 
        PROG x P cs C Q ((SEP_F,f) INSERT Z) = PROG x P cs C Q Z``,
  INIT_TAC \\ REWRITE_TAC [PROG_def] 
  \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ ASM_SIMP_TAC std_ss [UNDISCH (GPROG_FALSE_POST')]);

val PROG_STRENGTHEN_PRE = store_thm("PROG_STRENGTHEN_PRE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P P' cs C Q Z.
        SEP_IMP P' P /\ PROG x P cs C Q Z ==> PROG x P' cs C Q Z``,
  INIT_TAC \\ REWRITE_TAC [PROG_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (UNDISCH (GPROG_STRENGTHEN_PRE'))
  \\ Q.EXISTS_TAC `P` \\ ASM_SIMP_TAC std_ss []);

val PROG_WEAKEN_POST1 = store_thm("PROG_WEAKEN_POST1",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P cs C Q Q' Z.
        SEP_IMP Q Q' /\ PROG x P cs C Q Z ==> PROG x P cs C Q' Z``,
  INIT_TAC \\ REWRITE_TAC [PROG_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (UNDISCH (GPROG_WEAKEN_POST'))
  \\ Q.EXISTS_TAC `Q` \\ ASM_SIMP_TAC std_ss []);

val PROG_WEAKEN_POST = store_thm("PROG_WEAKEN_POST",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P cs C Q Q' f Z.
        SEP_IMP Q' Q'' /\ PROG x P cs C Q ((Q',f) INSERT Z) ==> 
        PROG x P cs C Q ((Q'',f) INSERT Z)``,
  INIT_TAC \\ REWRITE_TAC [PROG_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ MATCH_MP_TAC (UNDISCH (GPROG_WEAKEN_POST'))
  \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ Q.EXISTS_TAC `Q'` \\ ASM_SIMP_TAC std_ss [])

val PROG_HIDE_PRE = store_thm("PROG_HIDE_PRE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P P' cs C Q Z. 
        (!y:'var. PROG x (P * P' y) cs C Q Z) = PROG x (P * ~ P') cs C Q Z``,
  INIT_TAC
  \\ SIMP_TAC (bool_ss++sep_ss) [PROG_def,GPROG_def,BIGD_INSERT,BIGD_EMPTY] 
  \\ MOVE_STAR_TAC `p*p'*m*pp` `p*m*pp*p'`
  \\ ASM_SIMP_TAC std_ss [GSYM RUN_HIDE_PRE']
  \\ METIS_TAC []);

val PROG_HIDE_POST1 = store_thm("PROG_HIDE_POST1",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P cs C Q Q' y:'var Z. 
        PROG x P cs C (Q * Q' y) Z ==> PROG x P cs C (Q * ~ Q') Z``,
  METIS_TAC [PROG_WEAKEN_POST1,SEP_HIDE_INTRO]);

val PROG_HIDE_POST = store_thm("PROG_HIDE_POST",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P cs C Q Q' Q'' y:'var Z. 
        PROG x P cs C Q ((Q' * Q'' y,f) INSERT Z) ==> 
        PROG x P cs C Q ((Q' * ~ Q'',f) INSERT Z)``,
  METIS_TAC [PROG_WEAKEN_POST,SEP_HIDE_INTRO]);

val PROG_EXISTS_PRE = store_thm("PROG_EXISTS_PRE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P cs C Q Z. 
        (!y:'var. PROG x (P y) cs C Q Z) = PROG x (SEP_EXISTS y. P y) cs C Q Z``,
  INIT_TAC \\ REWRITE_TAC [GSYM SEP_HIDE_THM] \\ REPEAT STRIP_TAC
  \\ ASSUME_TAC ((Q.INST [`P`|->`emp`,`P'`|->`P`] o SPEC_ALL o UNDISCH o RES_SPEC') PROG_HIDE_PRE)
  \\ FULL_SIMP_TAC std_ss [emp_STAR]);

val PROG_ADD_CODE = store_thm("PROG_ADD_CODE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P cs C Q Z.
        PROG x P cs C Q Z ==> !C'. PROG x P cs (C UNION C') Q Z``,
  INIT_TAC \\ REWRITE_TAC [PROG_def]
  \\ ONCE_REWRITE_TAC [INSERT_SING_UNION]
  \\ REWRITE_TAC [UNION_ASSOC]
  \\ ASM_SIMP_TAC std_ss [GPROG_ADD_CODE']);

val PROG_MERGE_CODE = store_thm("PROG_MERGE_CODE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P cs c c' f C Q Z.
        PROG x P cs ((cs',f) INSERT (cs'',pcINC cs' o f) INSERT C) Q Z = 
        PROG x P cs ((cs'++cs'',f) INSERT  C) Q Z``,
  INIT_TAC \\ REWRITE_TAC [PROG_def]
  \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ ASM_SIMP_TAC std_ss [GSYM (UNDISCH GPROG_MERGE_CODE')]    
  \\ METIS_TAC [INSERT_COMM]);

val PROG_MOVE_COND = store_thm("PROG_MOVE_COND",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !c P cs C Q Z.
        PROG x (P * cond c) cs C Q Z = c ==> PROG x P cs C Q Z``, 
  INIT_TAC \\ REWRITE_TAC [PROG_def,GPROG_def,RUN_def,BIGD_INSERT,BIGD_EMPTY]
  \\ SIMP_TAC (bool_ss++sep_ss) [RES_FORALL]
  \\ MOVE_STAR_TAC `P * cond c * m * p * r` `P * m * p * r * cond c`
  \\ REWRITE_TAC [cond_STAR]
  \\ METIS_TAC []);

val PROG_COMPOSE_LEMMA = prove(
  ``!s x f cs. (x,f o pcINC cs) INSERT setINC cs s = setINC cs ((x,f) INSERT s)``,
  REWRITE_TAC [setINC_def,setADD_def,GSYM pcINC_def,setAPP_def]
  \\ ONCE_REWRITE_TAC [EXTENSION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [GSPECIFICATION,IN_INSERT] << [
    Q.EXISTS_TAC `(x,f)` \\ FULL_SIMP_TAC std_ss [],    
    Cases_on `x''` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [],
    Cases_on `x''` \\ FULL_SIMP_TAC std_ss []
    \\ DISJ2_TAC \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []]);

val PROG_COMPOSE = store_thm("PROG_COMPOSE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P M Q cs cs' C C' Z Z'. 
        PROG x P cs C M Z /\ PROG x M cs' C' Q Z' ==>
        PROG x P (cs ++ cs') (C UNION setINC cs C') Q (Z UNION setINC cs Z')``,
  INIT_TAC \\ REWRITE_TAC [PROG_def]
  \\ REPEAT STRIP_TAC  
  \\ ASM_SIMP_TAC std_ss [GSYM GPROG_MERGE_CODE']
  \\ CONV_TAC ((RATOR_CONV o RATOR_CONV o RAND_CONV) 
               (ONCE_REWRITE_CONV [GSYM (CONJUNCT2 UNION_EMPTY)]))
  \\ `!g f. (cs,I) INSERT (cs',g) INSERT C UNION f C' = 
            ((cs,I) INSERT C) UNION ((cs',g) INSERT f C')` by 
         SRW_TAC [] [EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY,AC (DISJ_COMM) (DISJ_ASSOC)]
  \\ `!g f. (Q,g) INSERT Z UNION f Z' = Z UNION ((Q,g) INSERT f Z')` by
         METIS_TAC [UNION_COMM,UNION_ASSOC,INSERT_SING_UNION]
  \\ ASM_REWRITE_TAC []   
  \\ MATCH_MP_TAC (UNDISCH GPROG_COMPOSE')
  \\ Q.EXISTS_TAC `{(M,pcINC cs)}`
  \\ STRIP_TAC
  THEN1 (ONCE_REWRITE_TAC [UNION_COMM] \\ ASM_REWRITE_TAC [Once (GSYM INSERT_SING_UNION)])
  \\ ONCE_REWRITE_TAC [UNION_COMM] 
  \\ REWRITE_TAC [GSYM INSERT_SING_UNION,UNION_EMPTY,pcINC_APPEND]
  \\ ONCE_REWRITE_TAC [GSYM (SIMP_CONV std_ss [] ``cs',I o pcINC cs``)]
  \\ REWRITE_TAC [GSYM (REWRITE_CONV [setINC_CLAUSES] ``setINC cs {(M,I)}``)]
  \\ REWRITE_TAC [GSYM (REWRITE_CONV [setINC_CLAUSES] ``setINC cs ((cs',f) INSERT C')``)]
  \\ REWRITE_TAC [setINC_def,setADD_def]  
  \\ MATCH_MP_TAC (UNDISCH GPROG_SHIFT')
  \\ ASM_REWRITE_TAC []);

val PROG_LOOP = store_thm("PROG_LOOP",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P Q cs C Z.
        (?R.
           WF R /\
           !v0:'var.
             PROG x (P v0) cs C Q
               (((SEP_EXISTS v. P v * cond (R v v0)),I) INSERT Z)) ==>
        !v0. PROG x (P v0) cs C Q Z``,
  INIT_TAC \\ REWRITE_TAC [PROG_def] \\ NTAC 6 STRIP_TAC
  \\ MATCH_MP_TAC (UNDISCH GPROG_LOOP1')
  \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ Q.EXISTS_TAC `R` \\ ASM_SIMP_TAC std_ss []);

val PROG_LOOP_MEASURE = store_thm("PROG_LOOP_MEASURE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !m:'var->num P Q cs C Z.
        (!v0:'var.
           PROG x (P v0) cs C Q
             (((SEP_EXISTS v. P v * cond (m v < m v0)),I) INSERT Z)) ==>
        !v0. PROG x (P v0) cs C Q Z``,
  INIT_TAC \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (UNDISCH (RES_SPEC' PROG_LOOP))
  \\ Q.EXISTS_TAC `measure m` 
  \\ FULL_SIMP_TAC bool_ss [prim_recTheory.WF_measure,
       prim_recTheory.measure_def,relationTheory.inv_image_def]);

val PROG_EXTRACT_POST = store_thm("PROG_EXTRACT_POST",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P Y Q cs C Z.
        PROG x P cs C Q Z = PROG x P cs C SEP_F ((Q,pcINC cs) INSERT Z)``,
  INIT_TAC \\ ASM_SIMP_TAC std_ss [PROG_def,UNDISCH GPROG_FALSE_POST']);

val PROG_EXTRACT_CODE = store_thm("PROG_EXTRACT_CODE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P Y Q cs C Z.
        PROG x P cs C SEP_F Z = PROG x P [] ((cs,I) INSERT C) SEP_F Z``,
  INIT_TAC \\ ASM_SIMP_TAC std_ss [PROG_def,GPROG_EMPTY_CODE',GPROG_FALSE_POST']);

val PROG_APPEND_CODE = store_thm("PROG_APPEND_CODE",
  ``!((x:('a,'b,'c)processor)::PROCESSORS). 
      !P Y Q cs C Z.
        PROG x P cs C SEP_F Z ==> !cs'. PROG x P (cs++cs') C SEP_F Z``,
  INIT_TAC \\ ASM_SIMP_TAC bool_ss [PROG_def,GPROG_FALSE_POST',GSYM GPROG_MERGE_CODE'] 
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ (CONV_TAC o RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [INSERT_SING_UNION])
  \\ PAT_ASSUM ``GPROG x Y C Z`` (ASSUME_TAC o MATCH_MP (UNDISCH GPROG_ADD_CODE'))
  \\ ONCE_REWRITE_TAC [UNION_COMM]
  \\ ASM_REWRITE_TAC []);

val PROG_INTRO = store_thm("PROG_INTRO",
  ``!set n pc i P cs Q Q' f.
      (!a b x y. (i (a,x) = i (b,y)) ==> (a = b)) /\ LENGTH cs <= dimword (:'b) ==>
      ((!p. RUN ((set,n,pc,i):('a,'b,'c)processor) 
        (P * msequence i p cs * pc p) 
        ((Q * msequence i p cs * pc (pcINC cs p)) \/ (Q' * msequence i p cs * pc (f p)))) =
       PROG (set,n,pc,i) P cs {} Q {(Q',f)})``,
  REWRITE_TAC [PROG_def,GPROG_def,BIGD_INSERT,BIGD_EMPTY,SEP_DISJ_CLAUSES]
  \\ REPEAT STRIP_TAC
  \\ ASSUME_TAC ((Q.GEN `p` o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o 
                  Q.SPECL [`cs`,`I`,`p`,`i`]) mpool_eq_msequence)
  \\ FULL_SIMP_TAC std_ss [mpool_eq_msequence]);


(* ----------------------------------------------------------------------------- *)
(* Theorems for PROC                                                             *)
(* ----------------------------------------------------------------------------- *)

val PROC_CALL = store_thm("PROC_CALL",
  ``!((x:('a,'b,'c)processor)::PROCESSORS) lr P' j f P Q C. 
      CALL x lr P' cs f /\ PROC x lr P Q C ==>
      PROG x (P * P') cs (setAPP f C) Q {}``,
  INIT_TAC 
  \\ SIMP_TAC std_ss [CALL_def,PROG_def,PROC_def,GPROG_def,BIGD_INSERT,BIGD_EMPTY,
                      SEP_DISJ_CLAUSES,F_STAR,mpool_EMPTY_INSERT,RUN_def,RES_FORALL]
  \\ ONCE_REWRITE_TAC [INSERT_SING_UNION]
  \\ REWRITE_TAC [UNION_EMPTY]
  \\ REPEAT STRIP_TAC
  \\ `?X. mpool i p ({(cs,I)} UNION setAPP f C) = mpool i p ({(cs,I)}) * X`  
         by METIS_TAC [mpool_EXTEND]
  \\ FULL_SIMP_TAC std_ss []
  \\ ASM_MOVE_STAR_TAC `p*p'*(m*x)*pp*r` `p'*pp*m*(x*r*p)`
  \\ PAT_ASSUM ``!p:'a s:'b. b ==> b'`` 
       (STRIP_ASSUME_TAC o UNDISCH o Q.SPEC `X * R * P` o UNDISCH o SPEC_ALL)
  \\ ASM_MOVE_STAR_TAC `lr*pp*m*(x*r*p)` `lr*pp*(m*x)*r*p`
  \\ `?Y. mpool i p {(cs,I)} * X = mpool i p (setAPP f C) * Y` 
           by METIS_TAC [mpool_EXTEND,UNION_COMM]
  \\ FULL_SIMP_TAC std_ss []
  \\ ASM_MOVE_STAR_TAC `lr*pp*(m*y)*r*p` `p*lr*m*pp*(y*r)` 
  \\ `run n (k,s) IN set` by METIS_TAC [run_IN_set]
  \\ PAT_ASSUM ``!q:'a. b`` 
       (STRIP_ASSUME_TAC o UNDISCH o Q.SPEC `Y * R` o REWRITE_RULE [mpool_APP] o
        UNDISCH o Q.SPECL [`pcINC (cs:'c list) p`,`f (p:'b word)`,`run n (k,s)`])
  \\ FULL_SIMP_TAC std_ss [pcSET_def]
  \\ Q.EXISTS_TAC `k' + k`
  \\ MOVE_STAR_TAC `q*(m*y)*pp*r` `q*m*pp*(y*r)`
  \\ ASM_REWRITE_TAC [GSYM run_ADD]);

val PROG_RECURSION = store_thm("PROC_RECURSION",
  ``!P v. (!x C'. (!y. v y < (v x):num ==> P C' y) ==> P (C UNION C') x) ==> !x. P C x``,
  REPEAT STRIP_TAC \\ completeInduct_on `v x` \\ METIS_TAC [UNION_IDEMPOT]);


val _ = export_theory();
