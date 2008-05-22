
(* 
  set_trace "pp_unambiguous_comprehensions" 1;
*)

open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory wordsTheory arithmeticTheory listTheory pairTheory;

open set_sepTheory set_sepLib;


val _ = new_theory "prog";

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val _ = Parse.hide "set";


(* ----------------------------------------------------------------------------- *)
(* Definitions                                                                   *)
(* ----------------------------------------------------------------------------- *)

val _ = type_abbrev("processor",
  ``:('a set set)#
     ('a set -> 'a set -> bool)#
     ('b word -> 'a set -> bool)#
     ('b word # 'c -> 'a set -> bool)``);

val PROCESSORS_def = Define `
  PROCESSORS = 
    { (Z,next,pc,inst) |(Z,next,pc,inst)| !s s'. s IN Z /\ next s s' ==> s' IN Z } 
      : ('a,'b,'c) processor set`;

val run_def = Define `
  (run next (0,s) = s) /\ 
  (run next (SUC k,s) = run next (k, next s))`;

(* doesn't work
val rel_eventually_def = Define `
  (rel_eventually Q s n 0 = Q s) /\
  (rel_eventually Q s n (SUC k) = Q s \/ !s'. n s s' ==> rel_eventually Q s' n k)`;
*)
  
val rel_sequence_def = Define `
  rel_sequence R f s =
    (f 0 = s) /\ !n. if (?s. R (f n) s) then R (f n) (f (SUC n)) else (f (SUC n) = f n)`;

val seq_shift_def = Define `
  seq_shift (seq:num->'a) i = \j. (seq (i + j)):'a`;

val RUN_def = Define `
  RUN ((set,n,p,i):('a,'b,'c)processor) P Q = 
    !(s::set) R. (P * R) s ==> 
      (set,n,p,i) IN PROCESSORS /\ 
      !seq. rel_sequence n seq s ==> ?i. (Q * R) (seq i)`;

val msequence_def = Define `
  (msequence i a [] = emp) /\ 
  (msequence i a (x::xs) = i (a,x) * msequence i (a+1w) xs)`;

val mset_def = Define `
  mset i p (cs,f) = { i (f p + n2w k,c) |(c,k)| k < LENGTH cs /\ (c = EL k cs) }`;

val mpool_def = Define `
  mpool i p Z = BIGSTAR (BIGUNION { mset i p z |z| z IN Z })`;

val wLENGTH_def = Define `wLENGTH cs = n2w (LENGTH cs)`;

val pcSET_def = Define `pcSET x = \p. x:bool**'a`;
val pcADD_def = Define `pcADD (n:'a word) = \p. n + p`;
val pcINC_def = Define `pcINC c = pcADD (wLENGTH c)`;

val setAPP_def = Define `setAPP g Z = { (Q,f o g) |(Q,f)| (Q,f) IN Z }`;
val setADD_def = Define `setADD k Z = setAPP (pcADD k) Z`;
val setINC_def = Define `setINC c Z = setADD (wLENGTH c) Z`;
val setSTAR_def = Define `setSTAR (R:'a set ->bool) Z = { (Q * R,f) |(Q,f)| (Q,f) IN Z }`;

val GPROG_DISJ_def = Define `
  GPROG_DISJ i pc p C Y = SEP_BIGDISJ { P * mpool i p C * pc (f p) | (P,f) IN Y }`;

val GPROG_def = Define `
  GPROG ((set,n,pc,i):('a,'b,'c)processor) (Y:(('a set->bool)#('b word->'b word)) set) C Z =
    !p. RUN (set,n,pc,i) (GPROG_DISJ i pc p C Y) (GPROG_DISJ i pc p C Z)`;

val PROG_def = Define `
  PROG (x:('a,'b,'c)processor) P cs C Q Z =
    GPROG x {(P,I)} ((cs,I) INSERT C) ((Q,pcINC cs) INSERT Z)`;

val PROC_def = Define `
  PROC ((set,n,pc,i):('a,'b,'c)processor) lr P Q C =
    !q. PROG (set,n,pc,i) (P * lr q) [] C SEP_F {(Q,pcSET q)}`;

val CALL_def = Define `
  CALL ((set,n,pc,i):('a,'b,'c)processor) lr P cs f = 
    !p. RUN (set,n,pc,i) 
          (P * pc p * mpool i p {(cs,I)}) 
          (lr (pcINC cs p) * pc (f p) * mpool i p {(cs,I)})`;


(* ----------------------------------------------------------------------------- *)
(* Properties of pc and set operations                                           *)
(* ----------------------------------------------------------------------------- *)

val pcADD_pcADD = store_thm("pcADD_pcADD",
  ``!k k'. pcADD k o pcADD k' = pcADD (k + k')``,
  SIMP_TAC std_ss [FUN_EQ_THM,pcADD_def,wLENGTH_def,WORD_ADD_ASSOC]);

val pcADD_pcINC = store_thm("pcADD_pcINC",
  ``!k xs:'a list. pcADD k o pcINC xs = pcADD (k + wLENGTH xs)``,
  REWRITE_TAC [GSYM pcADD_pcADD,pcINC_def]);

val pcINC_pcADD = store_thm("pcINC_pcADD",
  ``!k xs:'a list. pcINC xs o pcADD k = pcADD (k + wLENGTH xs)``,
  ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ REWRITE_TAC [GSYM pcADD_pcADD,pcINC_def]);

val pcINC_pcINC = store_thm("pcINC_pcINC",
  ``!xs:'a list ys. pcINC ys o pcINC xs = pcINC (xs++ys)``,
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
              (setADD k ((Q,f) INSERT Z) = (Q,f o (pcADD k)) INSERT setADD k Z) /\
              (setADD k (Z UNION Z') = setADD k Z UNION setADD k Z')``,
  REWRITE_TAC [setADD_def,setAPP_CLAUSES,setAPP_UNION]);

val setADD_UNION = store_thm("setADD_UNION",
  ``!k x y. setADD k (x UNION y) = setADD k x UNION setADD k y``,
  REWRITE_TAC [setADD_def,setAPP_UNION]);

val setADD_0 = store_thm("setADD_0",
  ``setADD 0w x = x``,SRW_TAC [] [setADD_def,FUN_EQ_THM,pcADD_0,setAPP_I]);

val setINC_CLAUSES = store_thm("setINC_CLAUSES",
  ``!cs Q f Z. (setINC cs {} = {}) /\ 
               (setINC cs ((Q,f) INSERT Z) = (Q,f o (pcINC cs)) INSERT setINC cs Z) /\
               (setINC cs (Z UNION Z') = setINC cs Z UNION setINC cs Z')``,
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

val rel_sequence_EQ_EXISTS_run = store_thm("rel_sequence_EQ_EXISTS_run",
  ``(!seq. rel_sequence (\s s'. f s = s') seq s ==> ?i. P (seq i)) = ?k. P (run f (k,s))``,
  `!i s. run f (i,f s) = f (run f (i,s))` by (Induct_on `i` \\ ASM_REWRITE_TAC [run_def])
  \\ EQ_TAC \\ REPEAT STRIP_TAC << [
    `rel_sequence (\s s'. f s = s') (\i. run f (i,s)) s` by ALL_TAC << [
      ASM_SIMP_TAC std_ss [rel_sequence_def,run_def],
      RES_TAC \\ FULL_SIMP_TAC bool_ss []],
    Q.EXISTS_TAC `k` \\ `!i. seq i = run f (i,s)` by ALL_TAC \\ ASM_REWRITE_TAC []
    \\ Induct \\ FULL_SIMP_TAC bool_ss [run_def,rel_sequence_def] \\ METIS_TAC []]);


(* ----------------------------------------------------------------------------- *)
(* Theorems for RUN                                                              *)
(* ----------------------------------------------------------------------------- *)

val INIT_TAC = Cases \\ Cases_on `r` \\ Cases_on `r'`
val RW = REWRITE_RULE

val RUN_FRAME = store_thm("RUN_FRAME",
  ``!x P Q. RUN x P Q ==> !R. RUN x (P * R) (Q * R)``,
  INIT_TAC \\ SIMP_TAC bool_ss [RUN_def,RES_FORALL,GSYM STAR_ASSOC]
  \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val RUN_FALSE_PRE = store_thm("RUN_FALSE_PRE",
  ``!x Q. RUN x SEP_F Q``,
  INIT_TAC \\ REWRITE_TAC [RUN_def,F_STAR] \\ SIMP_TAC std_ss [RES_FORALL,SEP_F_def]);

val RUN_STRENGTHEN_PRE = store_thm("RUN_STRENGTHEN_PRE",
  ``!x P P' Q. SEP_IMP P' P /\ RUN x P Q ==> RUN x P' Q``,
  INIT_TAC \\ SIMP_TAC bool_ss [RUN_def,RES_FORALL]
  \\ METIS_TAC [SEP_IMP_def,SEP_IMP_FRAME]);

val RUN_WEAKEN_POST = store_thm("RUN_WEAKEN_POST",
  ``!x P Q Q'. SEP_IMP Q Q' /\ RUN x P Q ==> RUN x P Q'``,
  INIT_TAC \\ SIMP_TAC bool_ss [RUN_def,RES_FORALL]
  \\ REPEAT STRIP_TAC THEN1 METIS_TAC [] \\ IMP_RES_TAC SEP_IMP_FRAME
  \\ METIS_TAC [SEP_IMP_def]);

val IN_PROCESSORS = prove(
  ``!set n t u. 
      (set,n,t,u) IN PROCESSORS /\ rel_sequence n seq s /\ s IN set ==> 
      !i. (seq i) IN set``,
  SIMP_TAC std_ss [PROCESSORS_def,GSPECIFICATION] \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
  \\ FULL_SIMP_TAC std_ss [rel_sequence_def] \\ Induct_on `i` \\ METIS_TAC []);

val rel_sequence_shift = prove(
  ``!n seq s. rel_sequence n seq s ==> !i. rel_sequence n (seq_shift seq i) (seq i)``,
  REWRITE_TAC [rel_sequence_def]
  \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [seq_shift_def]
  \\ Cases_on `?s. n (seq (i + n')) s` \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [ADD1,ADD_ASSOC] \\ METIS_TAC []);

val RUN_COMPOSE = store_thm("RUN_COMPOSE",
  ``!x P P' M Q Q'. RUN x P (Q \/ M) /\ RUN x (M \/ P') Q' ==> 
                    RUN x (P \/ P') (Q \/ Q')``,
  INIT_TAC \\ SIMP_TAC bool_ss [RUN_def,GSYM STAR_OVER_DISJ,RES_FORALL,SEP_DISJ_def]
  \\ REPEAT STRIP_TAC \\ `(q,q',q'',r) IN PROCESSORS` by METIS_TAC [SEP_DISJ_def] << [    
    `?i. (Q * R) (seq i) \/ (M * R) (seq i)` by METIS_TAC []
    THEN1 (Q.EXISTS_TAC `i` \\ ASM_REWRITE_TAC [])
    \\ `(seq i) IN q` by METIS_TAC [IN_PROCESSORS]
    \\ `rel_sequence q' (seq_shift seq i) (seq i)` by METIS_TAC [rel_sequence_shift]
    \\ `?j. (Q' * R) (seq_shift seq i j)` by METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [seq_shift_def] 
    \\ Q.EXISTS_TAC `i + j` \\ ASM_REWRITE_TAC [],    
    METIS_TAC []]);

val RUN_HIDE_PRE = store_thm("RUN_HIDE_PRE",
  ``!x P P' Q. (!y:'var. RUN x (P * P' y) Q) = RUN x (P * ~ P') Q``,
  INIT_TAC \\ REPEAT STRIP_TAC   
  \\ SIMP_TAC (bool_ss++sep2_ss) [RUN_def,RES_FORALL,SEP_HIDE_THM]
  \\ SIMP_TAC std_ss [SEP_EXISTS_THM] \\ EQ_TAC \\ METIS_TAC []);

val RUN_HIDE_POST = store_thm("RUN_HIDE_POST",
  ``!x P Q Q' y:'var. RUN x P (Q * Q' y) ==> RUN x P (Q * ~ Q')``,
  METIS_TAC [RUN_WEAKEN_POST,SEP_HIDE_INTRO]);

val RUN_MOVE_COND = store_thm("RUN_MOVE_COND",
  ``!x P Q c. c ==> RUN x P Q = RUN x (P * cond c) Q``,
  INIT_TAC \\ Cases_on `c` \\ REWRITE_TAC [RUN_def,SEP_cond_CLAUSES,emp_STAR,F_STAR]
  \\ REWRITE_TAC [SEP_F_def,RES_FORALL]);

val RUN_LOOP = store_thm("RUN_LOOP",
  ``!x Inv P Q.
      (?R. WF R /\ 
         !v:'var. RUN x (Inv v \/ P) (Q \/ SEP_EXISTS v'. Inv v' * cond (R v' v))) ==>
      (!v:'var. RUN x (Inv v \/ P) Q)``,
  INIT_TAC \\ NTAC 4 STRIP_TAC
  \\ recInduct (UNDISCH (SPEC_ALL relationTheory.WF_INDUCTION_THM))  
  \\ FULL_SIMP_TAC std_ss [RUN_def,RES_FORALL,GSYM STAR_OVER_DISJ] \\ REPEAT STRIP_TAC  
  \\ `(q,q',q'',r) IN PROCESSORS` by METIS_TAC [] \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC bool_ss [SEP_DISJ_def] \\ FULL_SIMP_TAC (bool_ss++sep2_ss) []
  \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,cond_STAR] << [
    `?i. (Q * R') (seq i) \/ ?y. R y x /\ (Inv y * R') (seq i)` by METIS_TAC []
    THEN1 (Q.EXISTS_TAC `i` \\ ASM_REWRITE_TAC [])
    \\ `(seq i) IN q` by METIS_TAC [IN_PROCESSORS]
    \\ `rel_sequence q' (seq_shift seq i) (seq i)` by METIS_TAC [rel_sequence_shift]
    \\ `?j. (Q * R') (seq_shift seq i j)` by METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [seq_shift_def] 
    \\ Q.EXISTS_TAC `i + j` \\ ASM_REWRITE_TAC [],
    `?i. (Q * R') (seq i) \/ ?y. R y x /\ (Inv y * R') (seq i)` by METIS_TAC []
    THEN1 (Q.EXISTS_TAC `i` \\ ASM_REWRITE_TAC [])
    \\ `(seq i) IN q` by METIS_TAC [IN_PROCESSORS]
    \\ `rel_sequence q' (seq_shift seq i) (seq i)` by METIS_TAC [rel_sequence_shift]
    \\ `?j. (Q * R') (seq_shift seq i j)` by METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [seq_shift_def] 
    \\ Q.EXISTS_TAC `i + j` \\ ASM_REWRITE_TAC []]);

val RUN_FRAME_LOOP = store_thm("RUN_FRAME_LOOP",
  ``!x:('a,'b,'c)processor. 
      (!y. RUN x (P y) (Q y \/ (P (g y) * h y))) ==>
      (!y s. P y s ==> m (g y) < (m y):num) ==>
      (!y. SEP_IMP (Q ((g:'d->'d) y) * h y) (Q y)) ==>
      (!y. RUN x (P y) (Q y))``,
  INIT_TAC \\ REPEAT STRIP_TAC \\ completeInduct_on `m y` \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [RUN_def,RES_FORALL] \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ Q.PAT_ASSUM `!y s. s IN set ==> !R. b` (STRIP_ASSUME_TAC o
       SIMP_RULE std_ss [SEP_DISJ_def] o REWRITE_RULE [GSYM STAR_OVER_DISJ] o 
       UNDISCH o Q.SPEC `R` o UNDISCH o Q.SPECL [`y`,`s`])
  \\ `?i. (Q y * R) (seq i) \/ (P (g y) * h y * R) (seq i)` by METIS_TAC []
  THEN1 (Q.EXISTS_TAC `i` \\ ASM_REWRITE_TAC [])
  \\ `m (g y) < m y` by   
    (Q.PAT_ASSUM `!y s. b` MATCH_MP_TAC
     \\ FULL_SIMP_TAC bool_ss [STAR_def] \\ METIS_TAC [])
  \\ `(seq i) IN q` by METIS_TAC [IN_PROCESSORS]
  \\ `rel_sequence q' (seq_shift seq i) (seq i)` by METIS_TAC [rel_sequence_shift]
  \\ Q.PAT_ASSUM `!m'. m' < m y ==> b` (STRIP_ASSUME_TAC o
     UNDISCH o REWRITE_RULE [STAR_ASSOC] o Q.SPECL [`h (y:'d) * R`] o
     UNDISCH o Q.SPEC `(seq :num -> 'a -> bool) (i :num)` o UNDISCH o RW [] o
     Q.SPECL [`m`,`g:'d->'d y`] o UNDISCH o Q.SPEC `m (g:'d->'d y)`)
  \\ `?j. (Q (g y) * h y * R) ((seq_shift seq i) j)` by METIS_TAC []
  \\ `SEP_IMP (Q (g y) * h y) (Q y)` by METIS_TAC []
  \\ IMP_RES_TAC SEP_IMP_FRAME
  \\ FULL_SIMP_TAC std_ss [seq_shift_def,SEP_IMP_def]
  \\ Q.EXISTS_TAC `i + j` \\ METIS_TAC []);

val RUN_REFL = store_thm("RUN_REFL",
  ``!x:('a,'b,'c)processor P. x IN PROCESSORS ==> RUN x P P``,
  INIT_TAC \\ SIMP_TAC std_ss [RUN_def,RES_FORALL] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `0` \\ FULL_SIMP_TAC bool_ss [rel_sequence_def]);


(* ----------------------------------------------------------------------------- *)
(* Theorems for GPROG                                                            *)
(* ----------------------------------------------------------------------------- *)

val GPROG_DISJ_FRAME = prove(
  ``!i pc p C Y R.
      GPROG_DISJ i pc p C (setSTAR R Y) = GPROG_DISJ i pc p C Y * R``,
  REWRITE_TAC [GPROG_DISJ_def,STAR_OVER_BIGDISJ,setSTAR_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ ONCE_REWRITE_TAC [EXTENSION]
  \\ SIMP_TAC bool_ss [GSPECIFICATION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss [] << [  
   Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
   \\ Q.EXISTS_TAC `q' * mpool i p C * pc (r' p)`
   \\ SIMP_TAC (bool_ss++star_ss) []
   \\ Q.EXISTS_TAC `(q',r')` \\ FULL_SIMP_TAC (std_ss++star_ss) [],
   Q.EXISTS_TAC `(q * R,r)` \\ FULL_SIMP_TAC (std_ss++star_ss) []
   \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC (std_ss++star_ss) []]);

val GPROG_DISJ_UNION = prove(
  ``!i pc p C Y Z. 
      GPROG_DISJ i pc p C (Y UNION Z) = 
      GPROG_DISJ i pc p C Y \/ GPROG_DISJ i pc p C Z``,
  REPEAT STRIP_TAC
  \\ REWRITE_TAC [GSYM SEP_BIGDISJ_CLAUSES,GPROG_DISJ_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ ONCE_REWRITE_TAC [EXTENSION]
  \\ SIMP_TAC std_ss [GSPECIFICATION,IN_UNION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss [] << [
    DISJ1_TAC \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [],
    DISJ2_TAC \\ Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [],
    Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss [], 
    Q.EXISTS_TAC `(q,r)` \\ FULL_SIMP_TAC std_ss []]);

val GPROG_DISJ_INSERT = prove(
  ``!i pc p C Q g Z.
      GPROG_DISJ i pc p C ((Q,g) INSERT Z) =
      Q * mpool i p C * pc (g p) \/ GPROG_DISJ i pc p C Z``,
  REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [INSERT_SING_UNION]
  \\ REWRITE_TAC [GPROG_DISJ_UNION] \\ REWRITE_TAC [GPROG_DISJ_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (x \/ z = y \/ (z:'a set -> bool))``)
  \\ `{P*mpool i p C * pc (f p) |(P,f)| (P,f) IN {(Q,g)}} = {Q*mpool i p C*pc (g p)}` by ALL_TAC
  \\ ASM_REWRITE_TAC [SEP_BIGDISJ_CLAUSES,SEP_DISJ_CLAUSES]
  \\ ONCE_REWRITE_TAC [EXTENSION]
  \\ SIMP_TAC std_ss [GSPECIFICATION,IN_UNION,IN_INSERT,NOT_IN_EMPTY]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  THEN1 (Cases_on `x'` \\ FULL_SIMP_TAC std_ss [])
  \\ Q.EXISTS_TAC `(Q,g)` \\ FULL_SIMP_TAC std_ss []);

val GPROG_DISJ_EMPTY = prove(
  ``!i pc p C. GPROG_DISJ i pc p C {} = SEP_F``,
  REWRITE_TAC [GSYM SEP_BIGDISJ_CLAUSES,GPROG_DISJ_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  \\ SRW_TAC [] [EXTENSION,GSPECIFICATION]  
  \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss []);

val GPROG_DISJ_CLAUSES = save_thm("GPROG_DISJ_CLAUSES",
  LIST_CONJ [GPROG_DISJ_UNION,GPROG_DISJ_INSERT,GPROG_DISJ_EMPTY,SEP_DISJ_CLAUSES]);

val GPROG_FRAME = store_thm("GPROG_FRAME",
  ``!x Y C Z. 
      GPROG x Y C Z ==> !R. GPROG x (setSTAR R Y) C (setSTAR R Z)``,
  INIT_TAC \\ ASM_SIMP_TAC std_ss [RUN_FRAME,GPROG_def,GPROG_DISJ_FRAME]);
    
val GPROG_ADD_CODE = store_thm("GPROG_ADD_CODE",
  ``!x Y C Z. GPROG x Y C Z ==> !C'. GPROG x Y (C UNION C') Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GPROG_DISJ_def] \\ REPEAT STRIP_TAC 
  \\ `?X. mpool r p (C UNION C') = mpool r p C * X` by METIS_TAC [mpool_EXTEND]
  \\ ASM_REWRITE_TAC [] \\ MOVE_STAR_TAC `x*(y*z)*q` `(x*y*q)*z` 
  \\ `!Y. SEP_BIGDISJ {P * mpool r p C * q'' (f p) * X | (P,f) | (P,f) IN Y} =
          SEP_BIGDISJ {P * mpool r p C * q'' (f p) | (P,f) | (P,f) IN Y} * X` by ALL_TAC << [
    STRIP_TAC \\ REWRITE_TAC [GSYM GPROG_DISJ_def,GSYM GPROG_DISJ_FRAME]
    \\ REWRITE_TAC [GPROG_DISJ_def,setSTAR_def] 
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
    \\ REWRITE_TAC [EXTENSION] \\ SIMP_TAC std_ss [GSPECIFICATION]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
    \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss [] << [
      Q.EXISTS_TAC `(q''' * X,r')` \\ FULL_SIMP_TAC (std_ss++star_ss) []
      \\ Q.EXISTS_TAC `(q''',r')` \\ FULL_SIMP_TAC (std_ss++star_ss) [],
      Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
      \\ Q.EXISTS_TAC `(q'''',r'')` \\ FULL_SIMP_TAC (std_ss++star_ss) []],
    ASM_REWRITE_TAC [] \\ ASM_SIMP_TAC std_ss [RUN_FRAME]]);

val GPROG_STRENGTHEN_PRE = store_thm("GPROG_STRENGTHEN_PRE",
  ``!x P P' Y C Z f.
        SEP_IMP P' P /\ GPROG x ((P,f) INSERT Y) C Z ==> GPROG x ((P',f) INSERT Y) C Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GPROG_DISJ_CLAUSES,GSYM STAR_ASSOC] 
  \\ REPEAT STRIP_TAC \\ PAT_ASSUM ``!p:'a. b`` (ASSUME_TAC o SPEC_ALL)
  \\ `!R X. SEP_IMP (P' * R \/ X)  (P * R \/ X)` by METIS_TAC [SEP_IMP_FRAME,SEP_IMP_MONO_DISJ]
  \\ MATCH_MP_TAC RUN_STRENGTHEN_PRE
  \\ METIS_TAC []);

val GPROG_DELETE_PRE = store_thm("GPROG_DELETE_PRE",
  ``!x Y Y' C Z. GPROG x (Y UNION Y') C Z ==> GPROG x Y C Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GPROG_DISJ_CLAUSES] \\ REPEAT STRIP_TAC
  \\ PAT_ASSUM ``!p:'a.b`` (ASSUME_TAC o SPEC_ALL)
  \\ MATCH_MP_TAC RUN_STRENGTHEN_PRE
  \\ Q.EXISTS_TAC `GPROG_DISJ r q'' p C Y \/ GPROG_DISJ r q'' p C Y'` 
  \\ ASM_REWRITE_TAC [] \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def]);

val GPROG_WEAKEN_POST = store_thm("GPROG_WEAKEN_POST",
  ``!x Y C Q Q' Z f.
      SEP_IMP Q Q' /\ GPROG x Y C ((Q,f) INSERT Z) ==> GPROG x Y C ((Q',f) INSERT Z)``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GPROG_DISJ_CLAUSES,GSYM STAR_ASSOC] 
  \\ REPEAT STRIP_TAC \\ PAT_ASSUM ``!p:'a. b`` (ASSUME_TAC o SPEC_ALL)
  \\ `!R X. SEP_IMP (Q * R \/ X)  (Q' * R \/ X)` by METIS_TAC [SEP_IMP_FRAME,SEP_IMP_MONO_DISJ]
  \\ MATCH_MP_TAC RUN_WEAKEN_POST
  \\ METIS_TAC []);

val GPROG_ADD_POST = store_thm("GPROG_ADD_POST",
  ``!x Y C Z. GPROG x Y C Z ==> !Z'. GPROG x Y C (Z UNION Z')``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GPROG_DISJ_CLAUSES] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC RUN_WEAKEN_POST
  \\ PAT_ASSUM ``!p:'a.b`` (ASSUME_TAC o SPEC_ALL)
  \\ Q.EXISTS_TAC `GPROG_DISJ r q'' p C Z` \\ ASM_REWRITE_TAC []
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def]);

val GPROG_FALSE_PRE = store_thm("GPROG_FALSE_PRE",
  ``!x f Y C Z. GPROG x ((SEP_F,f) INSERT Y) C Z = GPROG x Y C Z``,
  INIT_TAC \\ SIMP_TAC std_ss [GPROG_def,GPROG_DISJ_CLAUSES,F_STAR]);

val GPROG_FALSE_POST = store_thm("GPROG_FALSE_POST",
  ``!x f Y C Z. GPROG x Y C ((SEP_F,f) INSERT Z) = GPROG x Y C Z``,
  INIT_TAC \\ SIMP_TAC std_ss [GPROG_def,GPROG_DISJ_CLAUSES,F_STAR]);

val GPROG_EMPTY_CODE = store_thm("GPROG_EMPTY_CODE",
  ``!x f Y C Z.
      GPROG x Y (([],f) INSERT C) Z = GPROG x Y C Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,mpool_EMPTY_INSERT,GPROG_DISJ_def]);

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
  ``!x Y C Z. GPROG x Y C Z ==> !g. GPROG x (setAPP g Y) (setAPP g C) (setAPP g Z)``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GSYM mpool_APP,GPROG_DISJ_def] 
  \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [GPROG_SHIFT_LEMMA]);

val GPROG_MERGE_CODE = store_thm("GPROG_MERGE_CODE",
  ``!x cs cs' f Y C Z. 
      GPROG x Y ((cs,f) INSERT (cs',pcINC cs o f) INSERT C) Z  =
      GPROG x Y ((cs++cs',f) INSERT C) Z ``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,mpool_MERGE,UNION_ASSOC,GPROG_DISJ_def]);

val GPROG_MERGE_PRE = store_thm("GPROG_MERGE_PRE",
  ``!x P P' f Y C Z.
      GPROG x ((P,f) INSERT (P',f) INSERT Y) C Z = 
      GPROG x ((P \/ P',f) INSERT Y) C Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GPROG_DISJ_CLAUSES,SEP_DISJ_ASSOC,STAR_OVER_DISJ]);

val GPROG_MERGE_POST = store_thm("GPROG_MERGE_POST",
  ``!x Q Q' f Y C Z.
      GPROG x Y C ((Q,f) INSERT (Q',f) INSERT Z) = 
      GPROG x Y C ((Q \/ Q',f) INSERT Z)``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GPROG_DISJ_CLAUSES,SEP_DISJ_ASSOC,STAR_OVER_DISJ]);

val GPROG_COMPOSE = store_thm("GPROG_COMPOSE",
  ``!x Y Y' X C C' Z Z'. 
      GPROG x Y C (Z UNION X) /\ GPROG x (X UNION Y') C' Z' ==> 
      GPROG x (Y UNION Y') (C UNION C') (Z UNION Z')``,
  INIT_TAC \\ REPEAT STRIP_TAC 
  \\ `GPROG (q,q',q'',r) Y (C UNION C') (Z UNION X)` by METIS_TAC [GPROG_ADD_CODE]
  \\ `GPROG (q,q',q'',r) (X UNION Y') (C UNION C') Z'` 
         by METIS_TAC [GPROG_ADD_CODE, UNION_COMM]
  \\ FULL_SIMP_TAC std_ss [GPROG_def,GPROG_DISJ_CLAUSES]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC (RUN_COMPOSE) \\ METIS_TAC []);

val GPROG_SET_PC = store_thm("GPROG_SET_PC",
  ``!x Y C Z.
      (!p. GPROG x (setAPP (\x.p) Y) (setAPP (\x.p) C) (setAPP (\x.p) Z)) =
      GPROG x Y C Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GSYM mpool_APP,GPROG_DISJ_def] \\ REPEAT STRIP_TAC
  \\ `!Y p:'b word p':'b word. 
        {P * mpool r p C * q'' (f p') |(P,f)|(P,f) IN setAPP (\x. p) Y} = 
        {P * mpool r p C * q'' (f p)  |(P,f)|(P,f) IN Y}` by ALL_TAC
  \\ ASM_REWRITE_TAC []
  \\ ONCE_REWRITE_TAC [EXTENSION]
  \\ SIMP_TAC std_ss [setAPP_def,GSPECIFICATION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC << [   
    Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(q',r'')` \\ FULL_SIMP_TAC std_ss [],
    Cases_on `x'` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(q,r' o (\x.p))` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(q,r')` \\ FULL_SIMP_TAC std_ss []]);

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
  ``!x P g f Y C Z .
      GPROG x (((SEP_EXISTS y. P y * cond (g y)),f) INSERT Z) C Z =
      GPROG x ({(P y,f) |y| g y } UNION Z) C Z``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GPROG_DISJ_CLAUSES]
  \\ REWRITE_TAC [PRE_EXISTS_LEMMA,GPROG_DISJ_def]);

val GPROG_POST_EXISTS = store_thm("GPROG_POST_EXISTS",
  ``!x P g f Y C Z .
      GPROG x Y C (((SEP_EXISTS y. P y * cond (g y)),f) INSERT Z) =
      GPROG x Y C ({(P y,f) |y| g y } UNION Z)``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GPROG_DISJ_CLAUSES]
  \\ REWRITE_TAC [PRE_EXISTS_LEMMA,GPROG_DISJ_def]);

val GPROG_LOOP = store_thm("GPROG_LOOP",
  ``!x Inv Y C Z.
      (?R. WF R /\ 
         !v:'var. GPROG x (Inv v UNION Y) C (Z UNION {i|(i,v')|i IN Inv v' /\ R v' v })) ==>
      (!v:'var. GPROG x (Inv v UNION Y) C Z)``,
  INIT_TAC \\ REWRITE_TAC [GPROG_def,GPROG_DISJ_CLAUSES] \\ REWRITE_TAC [GPROG_DISJ_def]
  \\ ONCE_REWRITE_TAC 
      [(GSYM o BETA_CONV) 
       ``(\v. SEP_BIGDISJ {P * mpool r p C * q'' (f p) | (P,f) | (P,f) IN Inv v}) v``]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC RUN_LOOP
  \\ Q.EXISTS_TAC `R` \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC RUN_WEAKEN_POST
  \\ Q.EXISTS_TAC 
       `SEP_BIGDISJ {P * mpool r p C * q'' (f p) | (P,f) | (P,f) IN Z} \/
        SEP_BIGDISJ {P*mpool r p C * q'' (f p) |(P,f)|(P,f) IN {i|(i,v')|i IN Inv v' /\ R v' v}}`
  \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [SEP_DISJ_SYM]
  \\ MATCH_MP_TAC SEP_IMP_MONO_DISJ
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,SEP_BIGDISJ_def,GSPECIFICATION,cond_STAR]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `r''` \\ ASM_REWRITE_TAC [] 
  \\ Q.EXISTS_TAC `P` \\ ASM_REWRITE_TAC []
  \\ Q.EXISTS_TAC `(q''',r')` \\ FULL_SIMP_TAC std_ss []);

val GPROG_LOOP1 = store_thm("GPROG_LOOP1",
  ``!x f Inv Y C Z.
      (?R. WF R /\ 
         !v:'var. GPROG x ((Inv v,f) INSERT Y) C
                         (((SEP_EXISTS v'. Inv v' * cond(R v' v)),f) INSERT Z)) ==>
      (!v:'var. GPROG x ((Inv v,f) INSERT Y) C Z)``,
  INIT_TAC \\ NTAC 5 STRIP_TAC
  \\ ONCE_REWRITE_TAC [(GSYM o BETA_CONV) ``(\v. cond (R v' v)) v``]
  \\ ASM_SIMP_TAC bool_ss [GPROG_POST_EXISTS]
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
  \\ MATCH_MP_TAC GPROG_LOOP
  \\ Q.EXISTS_TAC `R` \\ ASM_REWRITE_TAC []);


(* ----------------------------------------------------------------------------- *)
(* Theorems for PROG                                                             *)
(* ----------------------------------------------------------------------------- *)

val PROG_FRAME = store_thm("PROG_FRAME",
  ``!x P cs C Q Z. 
        PROG x P cs C Q Z ==> !R. PROG x (P * R) cs C (Q * R) (setSTAR R Z)``,
  REWRITE_TAC [PROG_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC GPROG_FRAME \\ FULL_SIMP_TAC bool_ss [setSTAR_CLAUSES]);

val PROG_MERGE = store_thm("PROG_MERGE",
  ``!x P P' cs C C' Q Q' Z Z'. 
      PROG x P cs C Q Z /\ PROG x P' cs C' Q' Z' ==>
      PROG x (P \/ P') cs (C UNION C') (Q \/ Q') (Z UNION Z')``,
  REWRITE_TAC [PROG_def] \\ REPEAT STRIP_TAC
  \\ REWRITE_TAC [GSYM GPROG_MERGE_POST,GSYM GPROG_MERGE_PRE]
  \\ (IMP_RES_TAC o RW [UNION_EMPTY] o Q.INST [`X`|->`{}`,`Y`|->`{P,I}`] o SPEC_ALL) GPROG_COMPOSE
  \\ FULL_SIMP_TAC bool_ss [INSERT_UNION_EQ,INSERT_INSERT,UNION_EMPTY,UNION_IDEMPOT,
       (CONV_RULE (ONCE_REWRITE_CONV [UNION_COMM]) o SPEC_ALL) INSERT_UNION_EQ]);

val PROG_ABSORB_POST = store_thm("PROG_ABSORB_POST",
  ``!x P cs C Q Q' Z. 
      PROG x P cs C Q ((Q',pcINC cs) INSERT Z) = PROG x P cs C (Q \/ Q') Z``,
  INIT_TAC \\ ASM_SIMP_TAC std_ss [PROG_def,GPROG_MERGE_POST]);

val PROG_MERGE_POST = store_thm("PROG_MERGE_POST",
  ``!x P cs C Q f Q' Q'' Z. 
      PROG x P cs C Q ((Q',f) INSERT (Q'',f) INSERT Z) = 
      PROG x P cs C Q ((Q' \/ Q'',f) INSERT Z)``,
  REWRITE_TAC [PROG_def] \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ REWRITE_TAC [GSYM GPROG_MERGE_POST] \\ METIS_TAC [INSERT_COMM]);

val PROG_FALSE_PRE = store_thm("PROG_FALSE_PRE",
  ``!x cs C Q Z. PROG x SEP_F cs C Q Z = T``,
  INIT_TAC \\ ASM_SIMP_TAC bool_ss [PROG_def,GPROG_FALSE_PRE] 
  \\ REWRITE_TAC [GPROG_def,GPROG_DISJ_CLAUSES,RUN_def,F_STAR]
  \\ REWRITE_TAC [SEP_F_def,RES_FORALL]);

val PROG_FALSE_POST = store_thm("PROG_FALSE_POST",
  ``!x P cs C f Q Z. 
      PROG x P cs C Q ((SEP_F,f) INSERT Z) = PROG x P cs C Q Z``,
  INIT_TAC \\ REWRITE_TAC [PROG_def] \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ ASM_SIMP_TAC std_ss [GPROG_FALSE_POST]);

val PROG_STRENGTHEN_PRE = store_thm("PROG_STRENGTHEN_PRE",
  ``!x P cs C Q Z.
      PROG x P cs C Q Z ==> 
      !P'. SEP_IMP P' P ==> PROG x P' cs C Q Z``,
  REWRITE_TAC [PROG_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC GPROG_STRENGTHEN_PRE
  \\ Q.EXISTS_TAC `P` \\ ASM_SIMP_TAC std_ss []);

val PROG_PART_STRENGTHEN_PRE = store_thm("PROG_PART_STRENGTHEN_PRE",
  ``!x P P1 cs C Q Z.
      PROG x (P1 * P) cs C Q Z ==> 
      !P'. SEP_IMP P' P ==> PROG x (P1 * P') cs C Q Z``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC PROG_STRENGTHEN_PRE 
  \\ METIS_TAC [SEP_IMP_STAR,SEP_IMP_REFL]);

val PROG_WEAKEN_POST1 = store_thm("PROG_WEAKEN_POST1",
  ``!x P cs C Q Z.
      PROG x P cs C Q Z ==> 
      !Q'. SEP_IMP Q Q' ==> PROG x P cs C Q' Z``,
  REWRITE_TAC [PROG_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC GPROG_WEAKEN_POST
  \\ Q.EXISTS_TAC `Q` \\ ASM_SIMP_TAC std_ss []);

val PROG_PART_WEAKEN_POST1 = store_thm("PROG_PART_WEAKEN_POST1",
  ``!x P Q1 cs C Q Z.
      PROG x P cs C (Q1 * Q) Z ==> 
      !Q'. SEP_IMP Q Q' ==> PROG x P cs C (Q1 * Q') Z``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC PROG_WEAKEN_POST1 
  \\ METIS_TAC [SEP_IMP_STAR,SEP_IMP_REFL]);

val PROG_WEAKEN_POST = store_thm("PROG_WEAKEN_POST",
  ``!x P cs C Q Q' f Z.
      PROG x P cs C Q ((Q',f) INSERT Z) ==> 
      !Q''. SEP_IMP Q' Q'' ==> PROG x P cs C Q ((Q'',f) INSERT Z)``,
  REWRITE_TAC [PROG_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ MATCH_MP_TAC GPROG_WEAKEN_POST
  \\ Q.EXISTS_TAC `Q'` \\ ASM_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [INSERT_COMM] \\ ASM_REWRITE_TAC []);

val PROG_PART_WEAKEN_POST = store_thm("PROG_PART_WEAKEN_POST",
  ``!x P cs C Q Q' f Z.
      PROG x P cs C Q ((Q1 * Q',f) INSERT Z) ==> 
      !Q''. SEP_IMP Q' Q'' ==> PROG x P cs C Q ((Q1 * Q'',f) INSERT Z)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC PROG_WEAKEN_POST 
  \\ METIS_TAC [SEP_IMP_STAR,SEP_IMP_REFL]);

val PROG_HIDE_PRE = store_thm("PROG_HIDE_PRE",
  ``!x P P' cs C Q Z. 
      (!y:'var. PROG x (P * P' y) cs C Q Z) = PROG x (P * ~ P') cs C Q Z``,
  INIT_TAC \\ SIMP_TAC (bool_ss++sep_ss) [PROG_def,GPROG_def,GPROG_DISJ_CLAUSES] 
  \\ MOVE_STAR_TAC `p*p'*m*pp` `p*m*pp*p'`
  \\ ASM_SIMP_TAC std_ss [GSYM RUN_HIDE_PRE] \\ METIS_TAC []);

val PROG_HIDE_POST1 = store_thm("PROG_HIDE_POST1",
  ``!x P cs C Q Q' y:'var Z. 
      PROG x P cs C (Q * Q' y) Z ==> PROG x P cs C (Q * ~ Q') Z``,
  METIS_TAC [PROG_WEAKEN_POST1,SEP_HIDE_INTRO]);

val PROG_HIDE_POST = store_thm("PROG_HIDE_POST",
  ``!x P cs C Q Q' Q'' y:'var Z. 
      PROG x P cs C Q ((Q' * Q'' y,f) INSERT Z) ==> 
      PROG x P cs C Q ((Q' * ~ Q'',f) INSERT Z)``,
  METIS_TAC [PROG_WEAKEN_POST,SEP_HIDE_INTRO]);

val PROG_EXISTS_PRE = store_thm("PROG_EXISTS_PRE",
  ``!x P cs C Q Z. 
      (!y:'var. PROG x (P y) cs C Q Z) = PROG x (SEP_EXISTS y. P y) cs C Q Z``,
  INIT_TAC \\ REWRITE_TAC [GSYM SEP_HIDE_THM] \\ REPEAT STRIP_TAC
  \\ REWRITE_TAC [(RW [emp_STAR] o Q.INST [`P`|->`emp`] o SPEC_ALL) PROG_HIDE_PRE]);

val PROG_ADD_CODE = store_thm("PROG_ADD_CODE",
  ``!x P cs C Q Z. PROG x P cs C Q Z ==> !C'. PROG x P cs (C UNION C') Q Z``,
  REWRITE_TAC [PROG_def]
  \\ ONCE_REWRITE_TAC [INSERT_SING_UNION]
  \\ REWRITE_TAC [UNION_ASSOC]
  \\ ASM_SIMP_TAC std_ss [GPROG_ADD_CODE]);

val PROG_MERGE_CODE = store_thm("PROG_MERGE_CODE",
  ``!x P cs c c' f C Q Z.
      PROG x P cs ((cs',f) INSERT (cs'',pcINC cs' o f) INSERT C) Q Z = 
      PROG x P cs ((cs'++cs'',f) INSERT  C) Q Z``,
  INIT_TAC \\ REWRITE_TAC [PROG_def]
  \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ ASM_SIMP_TAC std_ss [GSYM GPROG_MERGE_CODE]    
  \\ METIS_TAC [INSERT_COMM]);

val PROG_MOVE_COND = store_thm("PROG_MOVE_COND",
  ``!x c P cs C Q Z.
      PROG x (P * cond c) cs C Q Z = c ==> PROG x P cs C Q Z``, 
  INIT_TAC \\ REWRITE_TAC [PROG_def,GPROG_def,RUN_def,GPROG_DISJ_CLAUSES]
  \\ SIMP_TAC (bool_ss++sep_ss) [RES_FORALL]
  \\ MOVE_STAR_TAC `P * cond c * m * p * r` `P * m * p * r * cond c`
  \\ REWRITE_TAC [cond_STAR] \\ METIS_TAC []);

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
  ``!x:('a,'b,'c)processor P M Q cs cs' C C' Z Z'. 
      PROG x P cs C M Z /\ PROG x M cs' C' Q Z' ==>
      PROG x P (cs ++ cs') (C UNION setINC cs C') Q (Z UNION setINC cs Z')``,
  REWRITE_TAC [PROG_def] \\ ONCE_REWRITE_TAC [CONJ_COMM]
  \\ ONCE_REWRITE_TAC [INSERT_SING_UNION] \\ ONCE_REWRITE_TAC [UNION_COMM]
  \\ REWRITE_TAC [GSYM AND_IMP_INTRO,UNION_EMPTY] \\ NTAC 11 STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o RW [setINC_CLAUSES] o 
       RW [GSYM setINC_def,pcINC_def,GSYM setADD_def] o 
       Q.SPEC `pcINC (cs:'c list)` o MATCH_MP GPROG_SHIFT)
  \\ FULL_SIMP_TAC std_ss [GSYM pcINC_def,pcINC_pcINC] \\ STRIP_TAC
  \\ (IMP_RES_TAC o RW [UNION_EMPTY] o Q.INST [`Y`|->`{(P,I)}`,`Y'`|->`{}`] o 
      SPEC_ALL) GPROG_COMPOSE
  \\ FULL_SIMP_TAC bool_ss [INSERT_UNION_EQ,INSERT_INSERT,UNION_EMPTY,UNION_IDEMPOT,
       (CONV_RULE (ONCE_REWRITE_CONV [UNION_COMM]) o SPEC_ALL) INSERT_UNION_EQ]
  \\ SIMP_TAC std_ss [GSYM GPROG_MERGE_CODE] \\ ASM_REWRITE_TAC [GSYM pcINC_pcINC]);
  
val PROG_COMPOSE_0 = store_thm("PROG_COMPOSE_0",
  ``!x P Q Q' cs C Z. 
      PROG x P cs C Q ((Q',pcADD 0w) INSERT Z) /\ PROG x Q' cs C Q Z ==>
      PROG x P cs C Q Z``,
  INIT_TAC \\ REWRITE_TAC [PROG_def,pcADD_0,GSYM AND_IMP_INTRO]
  \\ REWRITE_TAC [prove(``!x y z. x INSERT y INSERT z = (x INSERT z) UNION {y}``, 
    SIMP_TAC bool_ss [INSERT_UNION_EQ,ONCE_REWRITE_RULE[UNION_COMM]INSERT_UNION_EQ,UNION_EMPTY])]
  \\ NTAC 7 STRIP_TAC
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [GSYM (Q.ISPEC `{(Q',I)}` (CONJUNCT2 UNION_EMPTY))]))
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC GPROG_COMPOSE
  \\ FULL_SIMP_TAC bool_ss [UNION_IDEMPOT,UNION_EMPTY]);

val PROG_COMPOSE_I = store_thm("PROG_COMPOSE_I",
  ``!x P code C1 C2 Q1 Q2 Q4 Q5 Q6 Z1 Z2.
      PROG x (Q2 * Q6) code C2 Q4 Z2 ==>
      PROG x P code C1 Q1 ((Q2 * Q5,I) INSERT Z1) ==>
      SEP_IMP Q5 Q6 ==>
      PROG x P code (C1 UNION C2) (Q1 \/ Q4) (Z1 UNION Z2)``,
  ASM_SIMP_TAC bool_ss [PROG_def,GSYM GPROG_MERGE_POST]
  \\ ONCE_REWRITE_TAC [INSERT_COMM] \\ REPEAT STRIP_TAC
  \\ `SEP_IMP (Q2 * Q5) (Q2 * Q6)` by METIS_TAC [SEP_IMP_STAR,SEP_IMP_REFL]
  \\ IMP_RES_TAC GPROG_WEAKEN_POST
  \\ REPEAT (Q.PAT_ASSUM `!g.b` (fn th => ALL_TAC))
  \\ `!x. x INSERT C1 UNION C2 = (x INSERT C1) UNION (x INSERT C2)` by 
     (REWRITE_TAC [EXTENSION,IN_UNION,IN_INSERT] \\ METIS_TAC [])
  \\ `!x y. x INSERT y INSERT Z1 UNION Z2 = 
            (y INSERT Z1) UNION (x INSERT Z2)` by 
     (REWRITE_TAC [EXTENSION,IN_UNION,IN_INSERT] \\ METIS_TAC [])
  \\ ASM_REWRITE_TAC []
  \\ (MATCH_MP_TAC o REWRITE_RULE [UNION_EMPTY,UNION_IDEMPOT] o GEN_ALL o
      Q.SPECL [`x`,`Y`,`{}`,`{x}`,`C1`,`C2`,`Z1`,`Z2`]) GPROG_COMPOSE
  \\ Q.EXISTS_TAC `(Q2 * Q6,I)` \\ ASM_REWRITE_TAC []
  \\ ASM_REWRITE_TAC [GSYM (ONCE_REWRITE_RULE [UNION_COMM] INSERT_SING_UNION)]);

val PROG_EMPTY = store_thm("PROG_EMPTY",
  ``!x. x IN PROCESSORS ==> PROG x emp [] {} emp {}``,
  INIT_TAC \\ SIMP_TAC bool_ss [PROG_def,GPROG_def,pcINC_0,RUN_REFL,GPROG_def]);

val PROG_LOOP = store_thm("PROG_LOOP",
  ``!x P Q cs C Z.
      (?R.
         WF R /\
         !v0:'var.
           PROG x (P v0) cs C Q
             (((SEP_EXISTS v. P v * cond (R v v0)),I) INSERT Z)) ==>
      !v0. PROG x (P v0) cs C Q Z``,
  REWRITE_TAC [PROG_def] \\ NTAC 7 STRIP_TAC \\ MATCH_MP_TAC GPROG_LOOP1
  \\ ONCE_REWRITE_TAC [INSERT_COMM] \\ Q.EXISTS_TAC `R` \\ ASM_SIMP_TAC std_ss []);

val PROG_LOOP_MEASURE = store_thm("PROG_LOOP_MEASURE",
  ``!x m:'var->num P Q cs C Z.
      (!v0:'var.
         PROG x (P v0) cs C Q
           (((SEP_EXISTS v. P v * cond (m v < m v0)),I) INSERT Z)) ==>
      !v0. PROG x (P v0) cs C Q Z``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC PROG_LOOP
  \\ Q.EXISTS_TAC `measure m` 
  \\ FULL_SIMP_TAC bool_ss [prim_recTheory.WF_measure,
       prim_recTheory.measure_def,relationTheory.inv_image_def]);

val PROG_EXTRACT_POST = store_thm("PROG_EXTRACT_POST",
  ``!x P Y Q cs C Z.
      PROG x P cs C Q Z = PROG x P cs C SEP_F ((Q,pcINC cs) INSERT Z)``,
  ASM_SIMP_TAC std_ss [PROG_def,GPROG_FALSE_POST]);

val PROG_EXTRACT_CODE = store_thm("PROG_EXTRACT_CODE",
  ``!x P Y Q cs C Z.
      PROG x P cs C SEP_F Z = PROG x P [] ((cs,I) INSERT C) SEP_F Z``,
  ASM_SIMP_TAC std_ss [PROG_def,GPROG_EMPTY_CODE,GPROG_FALSE_POST]);

val PROG_APPEND_CODE = store_thm("PROG_APPEND_CODE",
  ``!x P Y Q cs C Z.
      PROG x P cs C SEP_F Z ==> !cs'. PROG x P (cs++cs') C SEP_F Z``,
  INIT_TAC \\ ASM_SIMP_TAC bool_ss [PROG_def,GPROG_FALSE_POST,GSYM GPROG_MERGE_CODE] 
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [INSERT_COMM]
  \\ (CONV_TAC o RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [INSERT_SING_UNION])
  \\ PAT_ASSUM ``GPROG x Y C Z`` (ASSUME_TAC o MATCH_MP GPROG_ADD_CODE)
  \\ ONCE_REWRITE_TAC [UNION_COMM]
  \\ ASM_REWRITE_TAC []);

val PROG_INTRO = store_thm("PROG_INTRO",
  ``!set n pc i P cs Q Q' f.
      (!a b x y. (i (a,x) = i (b,y)) ==> (a = b)) /\ LENGTH cs <= dimword (:'b) ==>
      ((!p. RUN ((set,n,pc,i):('a,'b,'c)processor) 
        (P * msequence i p cs * pc p) 
        ((Q * msequence i p cs * pc (pcINC cs p)) \/ (Q' * msequence i p cs * pc (f p)))) =
       PROG (set,n,pc,i) P cs {} Q {(Q',f)})``,
  REWRITE_TAC [PROG_def,GPROG_def,GPROG_DISJ_CLAUSES] \\ REPEAT STRIP_TAC
  \\ ASSUME_TAC ((Q.GEN `p` o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o 
                  Q.SPECL [`cs`,`I`,`p`,`i`]) mpool_eq_msequence)
  \\ FULL_SIMP_TAC std_ss [mpool_eq_msequence]);


(* ----------------------------------------------------------------------------- *)
(* Theorems for PROC                                                             *)
(* ----------------------------------------------------------------------------- *)

val PROC_CALL = store_thm("PROC_CALL",
  ``!x:('a,'b,'c)processor lr P' j f P Q C. 
      CALL x lr P' cs f /\ PROC x lr P Q C ==>
      PROG x (P * P') cs (setAPP f C) Q {}``,
  INIT_TAC \\ REWRITE_TAC [PROC_def] \\ REPEAT STRIP_TAC
  \\ REWRITE_TAC [PROG_def,GPROG_def,GPROG_DISJ_CLAUSES] \\ STRIP_TAC
  \\ MATCH_MP_TAC ((GEN_ALL o RW [SEP_DISJ_CLAUSES] o 
       Q.INST [`Q`|->`SEP_F`,`P'`|->`SEP_F`] o SPEC_ALL) RUN_COMPOSE)
  \\ Q.EXISTS_TAC `P * lr (pcINC cs p) * mpool r p ((cs,I) INSERT setAPP f C) * q'' (f p)`
  \\ ONCE_REWRITE_TAC [INSERT_SING_UNION]
  \\ `?X. mpool r p ({(cs,I)} UNION setAPP f C) = mpool r p ({(cs,I)}) * X`  
         by METIS_TAC [mpool_EXTEND] \\ FULL_SIMP_TAC bool_ss [] \\ STRIP_TAC << [
    FULL_SIMP_TAC std_ss [CALL_def]
    \\ MOVE_STAR_TAC `p*p'*(m*x)*q` `p'*m*q*(p*x)`
    \\ Q.SPEC_TAC (`P * X`,`fg`)    
    \\ MATCH_MP_TAC RUN_FRAME \\ FULL_SIMP_TAC (bool_ss++star_ss) [] \\ METIS_TAC [],
    Q.PAT_ASSUM `!c.b` (ASSUME_TAC o Q.SPEC `{(cs,I)}` o 
      ONCE_REWRITE_RULE [UNION_COMM] o MATCH_MP GPROG_ADD_CODE o 
      RW [setAPP_CLAUSES,GPROG_FALSE_POST] o
      Q.SPEC `f` o MATCH_MP GPROG_SHIFT o RW [PROG_def,GPROG_EMPTY_CODE] o 
      Q.SPEC `pcINC (cs:'c list) (p:'b word)`)
    \\ FULL_SIMP_TAC std_ss [GPROG_def,GPROG_DISJ_CLAUSES,pcSET_def]      
    \\ METIS_TAC []]);

val PROG_RECURSION = store_thm("PROC_RECURSION",
  ``!P v. (!x C'. (!y. v y < (v x):num ==> P C' y) ==> P (C UNION C') x) ==> !x. P C x``,
  REPEAT STRIP_TAC \\ completeInduct_on `v x` \\ METIS_TAC [UNION_IDEMPOT]);


(* ----------------------------------------------------------------------------- *)
(* Theorems for SPEC                                                             *)
(* ----------------------------------------------------------------------------- *)

val set_apply_def = Define `
  set_apply f set = { f x | x IN set }`;

val fix_pos_def = Define `
  fix_pos (x:'a,y:'b word) = (x,\z:'b word.y)`;

val SPEC_def = Define `
  SPEC (x:('a,'b,'c)processor) (P,p) C (Q,q) =
    GPROG x {(P,\x.p)} (set_apply fix_pos C) {(Q,\x.q)}`;

(* theorems *)

val IN_set_apply = prove(
  ``!x f s. x IN set_apply f s = ?a. (x = f a) /\ a IN s``,
  SIMP_TAC std_ss [GSPECIFICATION,set_apply_def]);

val set_apply_UNION = prove(
  ``!f x y. set_apply f (x UNION y) = set_apply f x UNION set_apply f y``,
  REWRITE_TAC [EXTENSION,IN_set_apply,IN_UNION] \\ METIS_TAC []);

val set_apply_CLAUSES = store_thm("set_apply_CLAUSES",
  ``!f x s.
      (set_apply f {} = {}) /\
      (set_apply f (x INSERT s) = f x INSERT set_apply f s)``,
  SIMP_TAC std_ss [EXTENSION,set_apply_def,GSPECIFICATION,NOT_IN_EMPTY,IN_INSERT]
  \\ METIS_TAC []);

(* SPEC theorems *)

val SPEC_FRAME = store_thm("SPEC_FRAME",
  ``!x P p C Q q. 
      SPEC x (P,p) C (Q,q) ==> !R. SPEC x (P * R,p) C (Q * R,q)``,
  REWRITE_TAC [SPEC_def,fix_pos_def] \\ REPEAT STRIP_TAC
  \\ MOVE_STAR_TAC `x*y*z` `x*z*y`
  \\ METIS_TAC [GPROG_FRAME,setSTAR_CLAUSES]);

val SPEC_FALSE_PRE = store_thm("SPEC_FALSE_PRE",
  ``!x P p C Q q. SPEC x (SEP_F,p) C (Q,q)``,
  INIT_TAC \\ REWRITE_TAC [SPEC_def,fix_pos_def,GPROG_FALSE_PRE]
  \\ REWRITE_TAC [GPROG_def,GPROG_DISJ_EMPTY,RUN_FALSE_PRE]);

val SPEC_STRENGTHEN = store_thm("SPEC_STRENGTHEN",
  ``!x P p C Q q. 
      SPEC x (P,p) C (Q,q) ==> 
      !P'. SEP_IMP P' P ==> SPEC x (P',p) C (Q,q)``,
  REWRITE_TAC [SPEC_def,fix_pos_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC GPROG_STRENGTHEN_PRE \\ Q.EXISTS_TAC `P`
  \\ ASM_SIMP_TAC std_ss []);

val SPEC_WEAKEN = store_thm("SPEC_WEAKEN",
  ``!x P p C Q q. 
      SPEC x (P,p) C (Q,q) ==> 
      !Q'. SEP_IMP Q Q' ==> SPEC x (P,p) C (Q',q)``,
  REWRITE_TAC [SPEC_def,fix_pos_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC GPROG_WEAKEN_POST \\ Q.EXISTS_TAC `Q`
  \\ ASM_SIMP_TAC std_ss []);

val SPEC_HIDE_PRE = store_thm("SPEC_HIDE_PRE",
  ``!x P P' p C Q q. 
      (!y:'var. SPEC x (P * P' y,p) C (Q,q)) = 
                SPEC x (P * ~ P',p) C (Q,q)``,
  INIT_TAC \\ REWRITE_TAC [SPEC_def,fix_pos_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (bool_ss++sep_ss) [GPROG_def,GPROG_DISJ_CLAUSES] 
  \\ MOVE_STAR_TAC `p*p'*m*pp` `p*m*pp*p'`
  \\ ASM_SIMP_TAC std_ss [GSYM RUN_HIDE_PRE] \\ METIS_TAC []);

val SPEC_HIDE_POST = store_thm("SPEC_HIDE_POST",
  ``!x P p cs c Q Q' y q Z. 
      SPEC x (P,p) C (Q * Q' y,q) ==> 
      SPEC x (P,p) C (Q * ~Q',q)``,
  METIS_TAC [SPEC_WEAKEN,SEP_HIDE_INTRO]);

val SPEC_MOVE_COND = store_thm("SPEC_MOVE_COND",
  ``!x g P p cs c Q q Z. 
      SPEC x (P * cond g,p) C (Q,q) = g ==> SPEC x (P,p) C (Q,q)``, 
  REPEAT STRIP_TAC \\ Cases_on `g` 
  \\ SIMP_TAC (bool_ss++sep2_ss) [SPEC_FALSE_PRE]);

val SPEC_COMPOSE = store_thm("SPEC_COMPOSE",
  ``!x P p C Q q C' Q' q'. 
      SPEC x (P,p) C (Q,q) ==> 
      SPEC x (Q,q) C' (Q',q') ==>
      SPEC x (P,p) (C UNION C') (Q',q')``,
  REWRITE_TAC [SPEC_def,set_apply_UNION]
  \\ REPEAT STRIP_TAC \\ (MATCH_MP_TAC o GEN_ALL o RW [UNION_EMPTY] o 
   Q.INST [`Z`|->`{}`,`Y'`|->`{}`] o SPEC_ALL) GPROG_COMPOSE
  \\ METIS_TAC []);

val SPEC_ADD_CODE = store_thm("SPEC_ADD_CODE",
  ``!x P p C Q q. 
      SPEC x (P,p) C (Q,q) ==> !C'. SPEC x (P,p) (C UNION C') (Q,q)``,
  REWRITE_TAC [SPEC_def,set_apply_UNION] \\ METIS_TAC [GPROG_ADD_CODE]);

val _ = export_theory();
