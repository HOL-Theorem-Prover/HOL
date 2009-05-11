
open HolKernel Parse boolLib bossLib; val _ = new_theory "sepOpsem";

open newOpsemTheory finite_mapTheory whileTheory arithmeticTheory pred_setTheory;


(* ====================================================================================== *)
(*  STANDARD DEFINITION OF SEPARATING CONJUNCTION: the *-operator                         *)
(* ====================================================================================== *)

val SPLIT_def = Define `SPLIT s (f,g) = (s = FUNION f g) /\ DISJOINT (FDOM f) (FDOM g)`;
val STAR_def = Define `STAR p q = (\s. ?f g. SPLIT s (f,g) /\ p f /\ q g)`;

val emp_def = Define `emp = \s. s = FEMPTY`;

val GEN_VAR_def = Define `
  GEN_VAR name value = \s:state. (s = (FEMPTY |+ (name,value)))`;

val VAR_def = Define `VAR name value = GEN_VAR name (Scalar value)`;
val ARRAY_def = Define `ARRAY name value = GEN_VAR name (Array value)`;

val _ = overload_on ("*",Term`STAR`);

(* theorems *)

val STAR_COMM = store_thm("STAR_COMM",
  ``!p q. p * q = q * p``,
  REWRITE_TAC [FUN_EQ_THM] THEN SIMP_TAC std_ss [STAR_def,SPLIT_def,DISJOINT_DEF]
  THEN REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss [EXTENSION,NOT_IN_EMPTY,IN_INTER]
  THEN (REVERSE (`FUNION f g = FUNION g f` by ALL_TAC) THEN1 METIS_TAC [])
  THEN REWRITE_TAC [GSYM SUBMAP_ANTISYM,SUBMAP_DEF,FUNION_DEF,IN_UNION]
  THEN METIS_TAC []);

val STAR_ASSOC_LEMMA = prove(
  ``!x p q r. (p * (q * r)) x ==> ((p * q) * r) x``,
  SIMP_TAC std_ss [STAR_def,SPLIT_def,DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY] 
  THEN REPEAT STRIP_TAC THEN Q.EXISTS_TAC `FUNION f f'` THEN Q.EXISTS_TAC `g'`
  THEN STRIP_TAC THEN ASM_REWRITE_TAC [] 
  THENL [ALL_TAC, Q.EXISTS_TAC `f` THEN Q.EXISTS_TAC `f'`]
  THEN FULL_SIMP_TAC std_ss [GSYM SUBMAP_ANTISYM,SUBMAP_DEF,FUNION_DEF,IN_UNION]
  THEN METIS_TAC []);

val STAR_ASSOC = store_thm("STAR_ASSOC",
  ``!p q r. p * (q * r) = (p * q) * r``,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN METIS_TAC [STAR_ASSOC_LEMMA,STAR_COMM]);

val emp_STAR = store_thm("emp_STAR",
  ``!p. ((emp * p) = p) /\ (p * emp = p)``,
  SIMP_TAC std_ss [STAR_def,SPLIT_def,emp_def,FDOM_FEMPTY,FUNION_FEMPTY_1,
    FUNION_FEMPTY_2,DISJOINT_EMPTY] THEN SIMP_TAC std_ss [FUN_EQ_THM]);

val GEN_VAR_STAR = store_thm("GEN_VAR_STAR",
  ``!v x p f. (GEN_VAR v x * p) f = v IN FDOM f /\ (f ' v = x) /\ p (f \\ v)``,
  SIMP_TAC std_ss [STAR_def,GEN_VAR_def,SPLIT_def,FDOM_FUPDATE,FDOM_FEMPTY]
  THEN REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC
  THENL [ALL_TAC, Q.EXISTS_TAC `f \\ v`]
  THEN ASM_SIMP_TAC std_ss [FUNION_DEF,IN_UNION,FDOM_FUPDATE,IN_INSERT,FAPPLY_FUPDATE_THM] THENL [
    REVERSE (`FUNION (FEMPTY |+ (v,x)) g \\ v = g` by ALL_TAC) THEN1 METIS_TAC []
    THEN FULL_SIMP_TAC std_ss [GSYM SUBMAP_ANTISYM,SUBMAP_DEF,FUNION_DEF,
      IN_UNION,FDOM_DOMSUB,IN_DELETE]
    THEN SIMP_TAC std_ss [DOMSUB_FAPPLY_THM]
    THEN SIMP_TAC std_ss [FUNION_DEF,FDOM_FUPDATE,IN_INSERT,FDOM_FEMPTY,NOT_IN_EMPTY]
    THEN FULL_SIMP_TAC std_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_INSERT]
    THEN METIS_TAC [],
    FULL_SIMP_TAC std_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_INSERT,FDOM_DOMSUB,IN_DELETE]
    THEN FULL_SIMP_TAC std_ss [GSYM SUBMAP_ANTISYM,SUBMAP_DEF,FUNION_DEF,
      IN_UNION,FDOM_DOMSUB,IN_DELETE]
    THEN SIMP_TAC std_ss [DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM]
    THEN SIMP_TAC std_ss [FUNION_DEF,FDOM_FUPDATE,IN_INSERT,FDOM_FEMPTY,NOT_IN_EMPTY]
    THEN METIS_TAC []]);   


(* ====================================================================================== *)
(*  PRECONDITION FOR LOOP                                                                 *)
(* ====================================================================================== *)

val PRE_def = Define `
  PRE f guard side (x:'a) = 
    (?n. ~guard (FUNPOW f n x)) /\
    (!k. (!m. m <= k ==> guard (FUNPOW f m x)) ==> side (FUNPOW f k x))`;

val PRE_THM = store_thm("PRE_THM",
  ``!f g p x. PRE f g p (x:'a) = g x ==> p x /\ PRE f g p (f x)``,
   REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC [PRE_def] THEN STRIP_TAC THENL [
     REWRITE_TAC [GSYM (hd (tl (CONJUNCTS FUNPOW)))]
     THEN Cases_on `n` THEN1 FULL_SIMP_TAC std_ss [FUNPOW] THEN REPEAT STRIP_TAC THENL [
       Q.PAT_ASSUM `!x.m` (ASSUME_TAC o
         SIMP_RULE std_ss [DECIDE ``m <= 0 = (m = 0:num)``] o Q.SPEC `0`)
       THEN FULL_SIMP_TAC std_ss [FUNPOW],
       Q.EXISTS_TAC `n'` THEN ASM_REWRITE_TAC [],
       Q.PAT_ASSUM `!k. (!m. m <= k ==> g (FUNPOW f m x)) ==> p (FUNPOW f k x)` MATCH_MP_TAC
       THEN Cases THEN ASM_SIMP_TAC std_ss [FUNPOW]],
     Cases_on `g x` THEN RES_TAC THENL [    
       FULL_SIMP_TAC bool_ss [GSYM (hd (tl (CONJUNCTS FUNPOW)))]
       THEN STRIP_TAC THEN1 METIS_TAC []
       THEN Cases THEN1 ASM_REWRITE_TAC [FUNPOW]
       THEN REPEAT STRIP_TAC              
       THEN Q.PAT_ASSUM `!k. pp ==> p (FUNPOW f (SUC k) x)` MATCH_MP_TAC
       THEN REPEAT STRIP_TAC
       THEN Q.PAT_ASSUM `!m. bb` (ASSUME_TAC o Q.SPEC `SUC m`)
       THEN FULL_SIMP_TAC std_ss [],
       STRIP_TAC THEN1 (Q.EXISTS_TAC `0` THEN ASM_REWRITE_TAC [FUNPOW])
       THEN REPEAT STRIP_TAC THEN Q.PAT_ASSUM `!m. bb` (MP_TAC o Q.SPEC `0`)
       THEN FULL_SIMP_TAC std_ss [FUNPOW]]]);

val PRE_INDUCT = store_thm("PRE_INDUCT",
  ``!P. (!x. g x /\ p x /\ P (f x) ==> P x) /\
        (!x. ~g x ==> P x) ==>
        (!x. PRE f g p x ==> P (x:'a))``,
  NTAC 4 STRIP_TAC THEN `?n. ~g (FUNPOW f n x)` by METIS_TAC [PRE_def]
  THEN Q.PAT_ASSUM `~g (FUNPOW f n x)` MP_TAC
  THEN Q.PAT_ASSUM `PRE f g p x` MP_TAC 
  THEN Q.SPEC_TAC (`x`,`x`) THEN Induct_on `n`
  THEN1 (REWRITE_TAC [FUNPOW] THEN REPEAT STRIP_TAC THEN METIS_TAC [PRE_THM])
  THEN FULL_SIMP_TAC std_ss [FUNPOW] THEN REPEAT STRIP_TAC THEN METIS_TAC [PRE_THM]);


(* ====================================================================================== *)
(*  SEPARATION LOGIC                                                                      *)
(* ====================================================================================== *)

val SEP_SPEC_def = Define `
  SEP_SPEC p c q = !r. SPEC (p * r) c (q * r)`;  

val SEP_TOTAL_SPEC_def = Define `
  SEP_TOTAL_SPEC p c q = !r. TOTAL_SPEC (p * r) c (q * r)`;  

val SEP_GUARD_def = Define `
  SEP_GUARD p g b = !r s x. (p x * r) s ==> (g x = beval b s)`;

val SEP_EXP_def = Define `
  SEP_EXP p e n = !r s x. (p x * r) s ==> (e x = neval n s)`;

val SEP_ARRAY_EXP_def = Define `
  SEP_ARRAY_EXP p e n = !r s x. (p x * r) s ==> (e x = aeval n s)`;


(* ====================================================================================== *)
(*  PARTIAL-CORRECTNESS THEOREMS                                                          *)
(* ====================================================================================== *)

val SEP_SPEC_FRAME = store_thm("SEP_SPEC_FRAME",
  ``!p c q. SEP_SPEC p c q ==> !r. SEP_SPEC (p * r) c (q * r)``,
  REWRITE_TAC [SEP_SPEC_def,GSYM STAR_ASSOC] THEN METIS_TAC []);

val SEP_SPEC_SEQ = store_thm("SEP_SPEC_SEQ",
  ``!p c1 m c2 q. SEP_SPEC p c1 m /\ SEP_SPEC m c2 q ==> SEP_SPEC p (Seq c1 c2) q``,
  REWRITE_TAC [SEP_SPEC_def,GSYM STAR_ASSOC] THEN METIS_TAC [SEQ_RULE]);

val SEP_SPEC_SKIP = store_thm("SEP_SPEC_SKIP",
  ``SEP_SPEC emp Skip emp``,
  SIMP_TAC std_ss [SEP_SPEC_def,SKIP_RULE]);

val SEP_SPEC_DISPOSE = store_thm("SEP_SPEC_DISPOSE",
  ``SEP_SPEC (GEN_VAR v x) (Dispose v) emp``,
  SIMP_TAC std_ss [SEP_SPEC_def,SPEC_def,DISPOSE_THM,GEN_VAR_STAR,emp_STAR]);

val SEP_SPEC_COND = store_thm("SEP_SPEC_COND",
  ``SEP_GUARD p g h ==>
    SEP_SPEC (p x) c1 (p y) ==>
    SEP_SPEC (p x) c2 (p z) ==>
    SEP_SPEC (p x) (Cond h c1 c2) (p (if g (x:'a) then y else z))``,
  REWRITE_TAC [SEP_SPEC_def] THEN REPEAT STRIP_TAC    
  THEN MATCH_MP_TAC COND_RULE THEN STRIP_TAC   
  THEN FULL_SIMP_TAC std_ss [SPEC_def,SEP_GUARD_def] 
  THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_SIMP_TAC std_ss []);  

val SEP_SPEC_ASSIGN = store_thm("SEP_SPEC_ASSIGN",
  ``!p v x z e y. 
       SEP_EXP (\x. VAR v (FST x) * p (SND x)) y e ==>
       SEP_SPEC (VAR v x * p z) (Assign v e) (VAR v (y (x,z)) * p z)``,
  SIMP_TAC std_ss [SEP_SPEC_def,SEP_EXP_def,GSYM STAR_ASSOC,VAR_def,GEN_VAR_STAR,SPEC_def]
  THEN REWRITE_TAC [Assign_def,GEN_ASSIGN_THM,Update_def,naeval_def ]
  THEN SIMP_TAC std_ss [FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_INSERT,DOMSUB_FUPDATE_THM] 
  THEN REPEAT STRIP_TAC
  THEN Q.PAT_ASSUM `!r.bb` (ASSUME_TAC o Q.SPECL [`r`,`s1`,`x,z`])
  THEN FULL_SIMP_TAC std_ss []);

val SEP_SPEC_ARRAY_ASSIGN = store_thm("SEP_SPEC_ARRAY_ASSIGN",
  ``!p v x z e1 e2 y1 y2. 
       SEP_EXP (\x. ARRAY v (FST x) * p (SND x)) y1 e1 ==>
       SEP_EXP (\x. ARRAY v (FST x) * p (SND x)) y2 e2 ==>
       SEP_SPEC (ARRAY v x * p z) (ArrayAssign v e1 e2) 
                (ARRAY v (x |+ (Num (y1 (x,z)), y2 (x,z))) * p z)``,
  SIMP_TAC std_ss [SEP_SPEC_def,SEP_EXP_def,GSYM STAR_ASSOC,ARRAY_def,GEN_VAR_STAR,SPEC_def]
  THEN REWRITE_TAC [ArrayAssign_def,GEN_ASSIGN_THM,Update_def,aeval_def,naeval_def]
  THEN SIMP_TAC std_ss [FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_INSERT,DOMSUB_FUPDATE_THM] 
  THEN REPEAT STRIP_TAC
  THEN REPEAT (Q.PAT_ASSUM `!r.bb` (ASSUME_TAC o Q.SPECL [`r`,`s1`,`(x,z)`]))
  THEN FULL_SIMP_TAC std_ss []
  THEN METIS_TAC [ArrayOf_def]);  

val SPEC_FALSE_PRE = prove(``!c q. SPEC (\s.F) c q``,SIMP_TAC std_ss [SPEC_def]);  

val While_SKIP_LEMMA = prove(
  ``!P b c. SPEC (\s. P s /\ ~beval b s) (While b c) P``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POST_WEAKEN
  THEN Q.EXISTS_TAC `(\s. P s /\ ~beval b s)` THEN SIMP_TAC std_ss [] 
  THEN ASSUME_TAC (SIMP_RULE std_ss [GSYM CONJ_ASSOC,METIS_PROVE [] ``~b /\ b = F``,SPEC_FALSE_PRE] 
    (Q.SPECL [`(\s. P s /\ ~beval b s)`,`b`] newOpsemTheory.WHILE_RULE))
  THEN METIS_TAC []);  

val While_STEP_LEMMA = prove(
  ``!p b c. SPEC (\s. p s /\ beval b s) c m /\ SPEC m (While b c) q ==>
            SPEC (\s. p s /\ beval b s) (While b c) q``,
  SIMP_TAC bool_ss [SPEC_def] THEN REPEAT STRIP_TAC
  THEN `?sM. EVAL c s sM /\ EVAL (While b c) sM s2` by METIS_TAC [WHILE_T_THM]
  THEN RES_TAC THEN RES_TAC THEN METIS_TAC []);  

val WHILE_LEMMA1 = prove( 
  ``!p. SEP_GUARD p g h ==> !x. ~g x ==> SEP_SPEC (p x) (While h c) (p x)``,
  STRIP_TAC THEN STRIP_TAC THEN FULL_SIMP_TAC std_ss [SEP_SPEC_def,SEP_GUARD_def]
  THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC PRE_STRENGTHEN
  THEN Q.EXISTS_TAC `\s. (p x * r) s /\ ~beval h s`
  THEN REVERSE STRIP_TAC THEN1 METIS_TAC [While_SKIP_LEMMA]           
  THEN SIMP_TAC std_ss [SEP_GUARD_def,beval_def]
  THEN METIS_TAC []);

val WHILE_LEMMA2 = prove( 
  ``SEP_GUARD p g h /\ g x /\ SEP_SPEC (p x) c (p (f x)) /\ SEP_SPEC (p (f x)) (While h c) q ==> 
    SEP_SPEC (p x) (While h c) q``,
  FULL_SIMP_TAC std_ss [SEP_SPEC_def]
  THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC PRE_STRENGTHEN THEN Q.EXISTS_TAC `\s. (p x * r) s /\ beval h s`
  THEN STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [SEP_GUARD_def] THEN METIS_TAC [])
  THEN MATCH_MP_TAC (GEN_ALL While_STEP_LEMMA)
  THEN Q.EXISTS_TAC `(p (f x) * r)` THEN ASM_SIMP_TAC std_ss []
  THEN MATCH_MP_TAC PRE_STRENGTHEN THEN Q.EXISTS_TAC `(p x * r)`
  THEN ASM_SIMP_TAC std_ss []);

val SEP_SPEC_WHILE = store_thm("SEP_SPEC_WHILE",
  ``SEP_GUARD p g h ==>
    (!x. SEP_SPEC (p x) c (p (f x))) ==>
    (!x. SEP_SPEC (p x) (While h c) (p (WHILE g f x)))``,
  REPEAT STRIP_TAC THEN Cases_on `?n. ~g (FUNPOW f n x)`
  THEN FULL_SIMP_TAC std_ss [] THENL [
    Q.PAT_ASSUM `~(g :'a -> bool) (FUNPOW (f :'a -> 'a) (n :num) (x :'a))` MP_TAC 
    THEN Q.SPEC_TAC (`x`,`x`)
    THEN Induct_on `n`
    THEN1 (ONCE_REWRITE_TAC [WHILE] THEN ASM_SIMP_TAC std_ss [FUNPOW] 
           THEN METIS_TAC [WHILE_LEMMA1])
    THEN STRIP_TAC THEN REVERSE (Cases_on `g x`)
    THEN ONCE_REWRITE_TAC [WHILE] THEN ASM_SIMP_TAC std_ss [FUNPOW] 
    THEN1 (METIS_TAC [WHILE_LEMMA1]) 
    THEN RES_TAC THEN STRIP_TAC    
    THEN MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] WHILE_LEMMA2)             
    THEN ASM_REWRITE_TAC [] THEN METIS_TAC [],
    FULL_SIMP_TAC bool_ss [SEP_SPEC_def] THEN STRIP_TAC
    THEN Q.ABBREV_TAC `invariant = \s. ?n. (p (FUNPOW f n x) * r) (s:state)`
    THEN MATCH_MP_TAC PRE_STRENGTHEN
    THEN Q.EXISTS_TAC `invariant`
    THEN STRIP_TAC THEN1
     (Q.UNABBREV_TAC `invariant`
      THEN SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC
      THEN Q.EXISTS_TAC `0` THEN ASM_SIMP_TAC std_ss [FUNPOW])
    THEN REVERSE (`SPEC invariant c invariant` by ALL_TAC) THENL [    
      MATCH_MP_TAC POST_WEAKEN      
      THEN Q.EXISTS_TAC `\s. invariant s /\ ~beval h s` THEN STRIP_TAC THENL [
        Q.UNABBREV_TAC `invariant` THEN SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC
        THEN `g (FUNPOW f n x)` by METIS_TAC []
        THEN METIS_TAC [SEP_GUARD_def],
        MATCH_MP_TAC (newOpsemTheory.WHILE_RULE)
        THEN MATCH_MP_TAC PRE_STRENGTHEN
        THEN Q.EXISTS_TAC `invariant` THEN ASM_SIMP_TAC std_ss []],
      Q.UNABBREV_TAC `invariant` THEN FULL_SIMP_TAC bool_ss [SPEC_def]
      THEN REPEAT STRIP_TAC
      THEN `g (FUNPOW f n x)` by METIS_TAC []
      THEN RES_TAC THEN Q.EXISTS_TAC `SUC n`
      THEN ASM_SIMP_TAC bool_ss [FUNPOW_SUC]]]);

val SEP_SPEC_THM = store_thm("SEP_SPEC_THM",
  ``SEP_SPEC p c q =
    !r s1. (p * r) s1 ==> !s2. EVAL c s1 s2 ==> (q * r) s2``,
  SIMP_TAC std_ss [SEP_SPEC_def,SPEC_def] THEN METIS_TAC []);


(* ====================================================================================== *)
(*  TOTAL-CORRECTNESS THEOREMS                                                            *)
(* ====================================================================================== *)

val SEP_TOTAL_SPEC_FRAME = store_thm("SEP_TOTAL_SPEC_FRAME",
  ``!p c q. SEP_TOTAL_SPEC p c q ==> !r. SEP_TOTAL_SPEC (p * r) c (q * r)``,
  REWRITE_TAC [SEP_TOTAL_SPEC_def,GSYM STAR_ASSOC] THEN METIS_TAC []);

val SEP_TOTAL_SPEC_SEQ = store_thm("SEP_TOTAL_SPEC_SEQ",
  ``!p c1 m c2 q. (s1 ==> SEP_TOTAL_SPEC p c1 m) /\ (s2 ==> SEP_TOTAL_SPEC m c2 q) ==> 
                  (s1 /\ s2 ==> SEP_TOTAL_SPEC p (Seq c1 c2) q)``,
  REWRITE_TAC [SEP_TOTAL_SPEC_def,GSYM STAR_ASSOC] THEN METIS_TAC [TOTAL_SEQ_RULE]);

val SEP_TOTAL_SPEC_SKIP = store_thm("SEP_TOTAL_SPEC_SKIP",
  ``SEP_TOTAL_SPEC emp Skip emp``,
  SIMP_TAC std_ss [SEP_TOTAL_SPEC_def,TOTAL_SKIP_RULE]);

val SEP_TOTAL_SPEC_COND = store_thm("SEP_TOTAL_SPEC_COND",
  ``SEP_GUARD p g h ==>
    (s1 ==> SEP_TOTAL_SPEC (p x) c1 (p y)) ==>
    (s2 ==> SEP_TOTAL_SPEC (p x) c2 (p z)) ==>
    (if g x then s1 else s2) ==>
    SEP_TOTAL_SPEC (p x) (Cond h c1 c2) (p (if g (x:'a) then y else z))``,
  Cases_on `g x` THEN ASM_REWRITE_TAC []
  THEN REWRITE_TAC [SEP_TOTAL_SPEC_def] THEN REPEAT STRIP_TAC    
  THEN MATCH_MP_TAC TOTAL_COND_RULE THEN STRIP_TAC THEN RES_TAC  
  THEN FULL_SIMP_TAC std_ss [TOTAL_SPEC_def,SPEC_def,SEP_GUARD_def] 
  THEN METIS_TAC []);

val SEP_TOTAL_GEN_ASSIGN_THM = store_thm("SEP_TOTAL_GEN_ASSIGN_THM",
  ``!P c v e Q. SEP_SPEC P (GenAssign v e) Q = SEP_TOTAL_SPEC P (GenAssign v e) Q``,
  REWRITE_TAC [SEP_SPEC_def,SEP_TOTAL_SPEC_def,TOTAL_GEN_ASSIGN_THM]);

val SEP_TOTAL_ASSIGN_THM = store_thm("SEP_TOTAL_ASSIGN_THM",
  ``!P c v e Q. SEP_SPEC P (Assign v e) Q = SEP_TOTAL_SPEC P (Assign v e) Q``,
  REWRITE_TAC [Assign_def,SEP_TOTAL_GEN_ASSIGN_THM]);

val SEP_TOTAL_ARRAY_ASSIGN_THM = store_thm("SEP_TOTAL_ARRAY_ASSIGN_THM",
  ``!P c v e Q. SEP_SPEC P (ArrayAssign v e1 e2) Q = SEP_TOTAL_SPEC P (ArrayAssign v e1 e2) Q``,
  REWRITE_TAC [ArrayAssign_def,SEP_TOTAL_GEN_ASSIGN_THM]);

val SEP_TOTAL_SPEC_WHILE = store_thm("SEP_TOTAL_SPEC_WHILE",
  ``SEP_GUARD p g h ==>
    (!x:'a. g x /\ side x ==> SEP_TOTAL_SPEC (p x) c (p (f x))) ==>
    (!x. PRE f g side x ==> SEP_TOTAL_SPEC (p x) (While h c) (p (WHILE g f x)))``,
  STRIP_TAC THEN STRIP_TAC
  THEN MATCH_MP_TAC (SIMP_RULE std_ss []
    (Q.SPEC `\x. SEP_TOTAL_SPEC (p x) (While h c) (p (WHILE g f x))` PRE_INDUCT))
  THEN REVERSE STRIP_TAC THEN FULL_SIMP_TAC std_ss [SEP_TOTAL_SPEC_def] THENL [
    ONCE_REWRITE_TAC [WHILE] THEN SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC
    THEN ASSUME_TAC (Q.SPECL [`p x * r`,`h`,`c`] TOTAL_WHILE_F_THM)
    THEN FULL_SIMP_TAC bool_ss [SEP_GUARD_def,TOTAL_SPEC_def,SPEC_def]
    THEN METIS_TAC [],
    REPEAT STRIP_TAC THEN RES_TAC
    THEN ASSUME_TAC (Q.SPECL [`p x * r`,`h`,`c`,`p ((f:'a->'a) x) * r`,`p (WHILE g f ((f:'a->'a) x)) * r`] TOTAL_WHILE_T_THM)
    THEN `TOTAL_SPEC (\s. (p x * r) s /\ beval h s) c (p (f x) * r)` by 
      (FULL_SIMP_TAC std_ss [TOTAL_SPEC_def,SPEC_def,SEP_GUARD_def] THEN METIS_TAC [])
    THEN `TOTAL_SPEC (p (f x) * r) (While h c) (p (WHILE g f (f x)) * r)` by METIS_TAC []
    THEN RES_TAC THEN `WHILE g f (f x) = WHILE g f x` by METIS_TAC [WHILE]
    THEN FULL_SIMP_TAC bool_ss [TOTAL_SPEC_def,SPEC_def,SEP_GUARD_def]
    THEN METIS_TAC []]);

val SEP_TOTAL_SPEC_THM = store_thm("SEP_TOTAL_SPEC_THM",
  ``SEP_TOTAL_SPEC p c q =
    !r s1. (p * r) s1 ==> (?s2. EVAL c s1 s2) /\
                          (!s2. EVAL c s1 s2 ==> (q * r) s2)``,
  SIMP_TAC std_ss [SEP_TOTAL_SPEC_def,TOTAL_SPEC_def,SPEC_def] THEN METIS_TAC []);

val _ = export_theory();
