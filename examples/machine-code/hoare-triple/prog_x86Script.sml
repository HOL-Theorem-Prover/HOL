
open HolKernel boolLib bossLib Parse;
open pred_setTheory res_quanTheory wordsTheory wordsLib bitTheory arithmeticTheory;
open listTheory pairTheory combinTheory addressTheory;

open set_sepTheory progTheory x86_Theory x86_seq_monadTheory;

val _ = new_theory "prog_x86";


infix \\ 
val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* ----------------------------------------------------------------------------- *)
(* The x86 set                                                                   *)
(* ----------------------------------------------------------------------------- *)

val _ = Hol_datatype `
  x86_el = xReg of Xreg => word32
          | xStatus of Xeflags => bool option
          | xEIP of word32
          | xMem of word32 => word8 option  `;

val x86_el_11 = DB.fetch "-" "x86_el_11";
val x86_el_distinct = DB.fetch "-" "x86_el_distinct";

val _ = Parse.type_abbrev("x86_set",``:x86_el set``);


(* ----------------------------------------------------------------------------- *)
(* Converting from x86-state tuple to x86_set                                    *)
(* ----------------------------------------------------------------------------- *)

val x86_2set'_def = Define `
  x86_2set' (rs,st,e,ms) s =
    IMAGE (\a. xReg a (XREAD_REG a s)) rs UNION
    IMAGE (\a. xStatus a (XREAD_EFLAG a s)) st UNION
    (if e then {xEIP (XREAD_EIP s)} else {}) UNION
    IMAGE (\a. xMem a (XREAD_MEM a s)) ms`;

val x86_2set_def   = Define `x86_2set s = x86_2set' (UNIV,UNIV,T,UNIV) s`;
val x86_2set''_def = Define `x86_2set'' x s = x86_2set s DIFF x86_2set' x s`;

(* theorems *)

val x86_2set'_SUBSET_x86_2set = prove(
  ``!y s. x86_2set' y s SUBSET x86_2set s``, 
  Cases_on `y` \\ Cases_on `r` \\ Cases_on `r'`
  \\ SIMP_TAC std_ss [SUBSET_DEF,x86_2set'_def,x86_2set_def,IN_IMAGE,IN_UNION,IN_UNIV]
  \\ METIS_TAC [NOT_IN_EMPTY]);

val SPLIT_x86_2set = prove(
  ``!x s. SPLIT (x86_2set s) (x86_2set' x s, x86_2set'' x s)``,
  REPEAT STRIP_TAC 
  \\ ASM_SIMP_TAC std_ss [SPLIT_def,EXTENSION,IN_UNION,IN_DIFF,x86_2set''_def]
  \\ `x86_2set' x s SUBSET x86_2set s` by METIS_TAC [x86_2set'_SUBSET_x86_2set]
  \\ SIMP_TAC bool_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_DIFF]
  \\ METIS_TAC [SUBSET_DEF]);

val SUBSET_x86_2set = prove(
  ``!u s. u SUBSET x86_2set s = ?y. u = x86_2set' y s``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [x86_2set'_SUBSET_x86_2set]
  \\ Q.EXISTS_TAC `({ a |a| ?x. xReg a x IN u },{ a |a| ?x. xStatus a x IN u },
                    (?x. xEIP x IN u),{ a |a| ?x. xMem a x IN u })`
  \\ FULL_SIMP_TAC std_ss [x86_2set'_def,x86_2set_def,EXTENSION,SUBSET_DEF,IN_IMAGE,
       IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,IN_UNIV]  
  \\ STRIP_TAC \\ ASM_REWRITE_TAC [] \\ EQ_TAC \\ REPEAT STRIP_TAC 
  THEN1 METIS_TAC [IN_INSERT,NOT_IN_EMPTY,x86_el_11,x86_el_distinct]
  THENL [ALL_TAC,ALL_TAC,Cases_on `?x. xEIP x IN u` \\ FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY],ALL_TAC]
  \\ PAT_ASSUM ``!x:'a. b:bool`` IMP_RES_TAC \\ FULL_SIMP_TAC std_ss [x86_el_11,x86_el_distinct]);

val SPLIT_x86_2set_EXISTS = prove(
  ``!s u v. SPLIT (x86_2set s) (u,v) = ?y. (u = x86_2set' y s) /\ (v = x86_2set'' y s)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [SPLIT_x86_2set] 
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def,x86_2set'_def,x86_2set''_def]
  \\ `u SUBSET (x86_2set s)` by 
       (FULL_SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [SUBSET_x86_2set] \\ Q.EXISTS_TAC `y` \\ REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_UNION,DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER]  
  \\ METIS_TAC []);

val PUSH_IN_INTO_IF = METIS_PROVE []
  ``!g x y z. x IN (if g then y else z) = if g then x IN y else x IN z``;

val IN_x86_2set = prove(``
  (!r x s. xReg r x IN (x86_2set s) = (x = XREAD_REG r s)) /\
  (!r x s. xReg r x IN (x86_2set' (rs,st,e,ms) s) = (x = XREAD_REG r s) /\ r IN rs) /\
  (!r x s. xReg r x IN (x86_2set'' (rs,st,e,ms) s) = (x = XREAD_REG r s) /\ ~(r IN rs)) /\
  (!a x s. xStatus a x IN (x86_2set s) = (x = XREAD_EFLAG a s)) /\
  (!a x s. xStatus a x IN (x86_2set' (rs,st,e,ms) s) = (x = XREAD_EFLAG a s) /\ a IN st) /\
  (!a x s. xStatus a x IN (x86_2set'' (rs,st,e,ms) s) = (x = XREAD_EFLAG a s) /\ ~(a IN st)) /\
  (!x s. xEIP x IN (x86_2set s) = (x = XREAD_EIP s)) /\
  (!x s. xEIP x IN (x86_2set' (rs,st,e,ms) s) = (x = XREAD_EIP s) /\ e) /\
  (!x s. xEIP x IN (x86_2set'' (rs,st,e,ms) s) = (x = XREAD_EIP s) /\ ~e) /\
  (!p x s. xMem p x IN (x86_2set s) = (x = XREAD_MEM p s)) /\
  (!p x s. xMem p x IN (x86_2set' (rs,st,e,ms) s) = (x = XREAD_MEM p s) /\ p IN ms) /\
  (!p x s. xMem p x IN (x86_2set'' (rs,st,e,ms) s) = (x = XREAD_MEM p s) /\ ~(p IN ms))``,
  SRW_TAC [] [x86_2set'_def,x86_2set''_def,x86_2set_def,IN_UNION,
     IN_INSERT,NOT_IN_EMPTY,IN_DIFF,PUSH_IN_INTO_IF] \\ METIS_TAC []);

val x86_2set''_11 = prove(
  ``!y y' s s'. (x86_2set'' y' s' = x86_2set'' y s) ==> (y = y')``,
  REPEAT STRIP_TAC \\ CCONTR_TAC
  \\ `?r st e m st. y = (r,st,e,m)` by METIS_TAC [PAIR]
  \\ `?r' st' e' m'. y' = (r',st',e',m')` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ] THENL [
    `?a. ~(a IN r = a IN r')` by METIS_TAC [EXTENSION]
    \\ `~((?x. xReg a x IN x86_2set'' y s) = (?x. xReg a x IN x86_2set'' y' s'))` by ALL_TAC,
    `?a. ~(a IN st = a IN st')` by METIS_TAC [EXTENSION]
    \\ `~((?x. xStatus a x IN x86_2set'' y s) = (?x. xStatus a x IN x86_2set'' y' s'))` by ALL_TAC,
    `~((?x. xEIP x IN x86_2set'' y s) = (?x. xEIP x IN x86_2set'' y' s'))` by ALL_TAC,
    `?a. ~(a IN m = a IN m')` by METIS_TAC [EXTENSION]
    \\ `~((?x. xMem a x IN x86_2set'' y s) = (?x. xMem a x IN x86_2set'' y' s'))` by ALL_TAC]
  \\ REPEAT (FULL_SIMP_TAC bool_ss [IN_x86_2set] \\ METIS_TAC [])
  \\ Q.PAT_ASSUM `x86_2set'' y' s' = x86_2set'' y s` (K ALL_TAC)     
  \\ FULL_SIMP_TAC bool_ss [IN_x86_2set] \\ METIS_TAC []);

val DELETE_x86_2set = prove(``
  (!a s. (x86_2set' (rs,st,ei,ms) (r,e,s,m)) DELETE xReg a (r a) =
         (x86_2set' (rs DELETE a,st,ei,ms) (r,e,s,m))) /\ 
  (!c s. (x86_2set' (rs,st,ei,ms) (r,e,s,m)) DELETE xStatus c (s c) =
         (x86_2set' (rs,st DELETE c,ei,ms) (r,e,s,m))) /\ 
  (!c s. (x86_2set' (rs,st,ei,ms) (r,e,s,m)) DELETE xEIP e =
         (x86_2set' (rs,st,F,ms) (r,e,s,m))) /\ 
  (!b s. (x86_2set' (rs,st,ei,ms) (r,e,s,m)) DELETE xMem b (m b) =
         (x86_2set' (rs,st,ei,ms DELETE b) (r,e,s,m)))``,
  SRW_TAC [] [x86_2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF,
    XREAD_REG_def,XREAD_MEM_def,XREAD_EFLAG_def,XREAD_EIP_def]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []);

val EMPTY_x86_2set = prove(``
  (x86_2set' (rs,st,e,ms) s = {}) = (rs = {}) /\ (ms = {}) /\ (st = {}) /\ ~e``,
  SRW_TAC [] [x86_2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,PUSH_IN_INTO_IF]
  \\ METIS_TAC []);
    

(* ----------------------------------------------------------------------------- *)
(* Defining the X86_MODEL                                                        *)
(* ----------------------------------------------------------------------------- *)

val xR1_def = Define `xR1 a x = SEP_EQ {xReg a x}`;
val xM1_def = Define `xM1 a x = SEP_EQ {xMem a x}`;
val xS1_def = Define `xS1 a x = SEP_EQ {xStatus a x}`;
val xPC_def = Define `xPC x = SEP_EQ {xEIP x}`;

val xS_def = Define `
  xS (x0,x1,x2,x3,x4,x5) = 
    xS1 X_CF x0 * xS1 X_PF x1 * xS1 X_AF x2 * 
    xS1 X_ZF x3 * xS1 X_SF x4 * xS1 X_OF x5`;

val X86_NEXT_REL_def = Define `X86_NEXT_REL s s' = (X86_NEXT s = SOME s')`;

val X86_INSTR_def    = Define `
  (X86_INSTR (a,[]) = {}) /\
  (X86_INSTR (a,c::cs) = xMem a (SOME ((b2w I (hex2bits c)):word8)) INSERT X86_INSTR (a+1w,cs))`;

val X86_MODEL_def = Define `X86_MODEL = (x86_2set, X86_NEXT_REL, X86_INSTR)`;

(* theorems *)

val lemma =
  METIS_PROVE [SPLIT_x86_2set]
  ``p (x86_2set' y s) ==> (?u v. SPLIT (x86_2set s) (u,v) /\ p u /\ (\v. v = x86_2set'' y s) v)``;

val X86_SPEC_SEMANTICS = store_thm("X86_SPEC_SEMANTICS",
  ``SPEC X86_MODEL p {} q =
    !y s seq. p (x86_2set' y s) /\ rel_sequence X86_NEXT_REL seq s ==>
              ?k. q (x86_2set' y (seq k)) /\ (x86_2set'' y s = x86_2set'' y (seq k))``,
  SIMP_TAC bool_ss [GSYM RUN_EQ_SPEC,RUN_def,X86_MODEL_def,STAR_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC bool_ss [SPLIT_x86_2set_EXISTS] \\ METIS_TAC [])    
  \\ Q.PAT_ASSUM `!s r. b` (STRIP_ASSUME_TAC o UNDISCH o SPEC_ALL o 
     (fn th => MATCH_MP th (UNDISCH lemma))  o Q.SPECL [`s`,`(\v. v = x86_2set'' y s)`])
  \\ FULL_SIMP_TAC bool_ss [SPLIT_x86_2set_EXISTS]
  \\ IMP_RES_TAC x86_2set''_11 \\ Q.EXISTS_TAC `i` \\ METIS_TAC []);


(* ----------------------------------------------------------------------------- *)
(* Theorems for construction of |- SPEC X86_MODEL ...                            *)
(* ----------------------------------------------------------------------------- *)

val STAR_x86_2set = store_thm("STAR_x86_2set",
  ``((xR1 a x * p) (x86_2set' (rs,st,ei,ms) (r,e,s,m)) =
      (x = r a) /\ a IN rs /\ p (x86_2set' (rs DELETE a,st,ei,ms) (r,e,s,m))) /\ 
    ((xS1 c z * p) (x86_2set' (rs,st,ei,ms) (r,e,s,m)) =
      (z = s c) /\ c IN st /\ p (x86_2set' (rs,st DELETE c,ei,ms) (r,e,s,m))) /\ 
    ((xPC q * p) (x86_2set' (rs,st,ei,ms) (r,e,s,m)) =
      (q = e) /\ ei /\ p (x86_2set' (rs,st,F,ms) (r,e,s,m))) /\ 
    ((xM1 b y * p) (x86_2set' (rs,st,ei,ms) (r,e,s,m)) =
      (y = m b) /\ b IN ms /\ p (x86_2set' (rs,st,ei,ms DELETE b) (r,e,s,m))) /\ 
    ((cond g * p) (x86_2set' (rs,st,ei,ms) (r,e,s,m)) =
      g /\ p (x86_2set' (rs,st,ei,ms) (r,e,s,m)))``,
  SIMP_TAC std_ss [xR1_def,xS1_def,xM1_def,EQ_STAR,INSERT_SUBSET,cond_STAR,xPC_def,XREAD_EIP_def,
    EMPTY_SUBSET,IN_x86_2set,XREAD_REG_def,XREAD_EFLAG_def,XREAD_MEM_def,GSYM DELETE_DEF]
  \\ METIS_TAC [DELETE_x86_2set]);

val CODE_POOL_x86_2set_AUX_LEMMA = prove(
  ``!x y z. ~(z IN y) ==> ((x = z INSERT y) = z IN x /\ (x DELETE z = y))``,
  SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DELETE] \\ METIS_TAC []);

val address_list_def = Define `
  (address_list a 0 = {}) /\
  (address_list a (SUC n) = a INSERT address_list (a+1w) n)`;

val x86_pool_def = Define `
  (x86_pool m p [] = T) /\
  (x86_pool m p (c::cs) = (SOME ((b2w I (hex2bits c)):word8) = m p) /\ 
                           x86_pool m (p+1w) cs)`;

val LEMMA1 = prove(
  ``!p q cs y. xMem p y IN X86_INSTR (q,cs) ==> ?k. k < LENGTH cs /\ (p = q + n2w k)``,
  Induct_on `cs` 
  \\ ASM_SIMP_TAC std_ss [X86_INSTR_def,EMPTY_SUBSET,LENGTH,NOT_IN_EMPTY,
       address_list_def,IN_INSERT,x86_el_11,n2w_11]  
  \\ REPEAT STRIP_TAC THEN1 (Q.EXISTS_TAC `0` \\ ASM_SIMP_TAC std_ss [WORD_ADD_0])
  \\ RES_TAC \\ Q.EXISTS_TAC `k + 1`
  \\ ASM_SIMP_TAC bool_ss [ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ STRIP_TAC THEN1 DECIDE_TAC \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM]);

val LEMMA2 = prove(
  ``!p q cs. p IN address_list q (LENGTH cs) ==> ?k. k < LENGTH cs /\ (p = q + n2w k)``,
  Induct_on `cs` 
  \\ ASM_SIMP_TAC std_ss [X86_INSTR_def,EMPTY_SUBSET,LENGTH,NOT_IN_EMPTY,
       address_list_def,IN_INSERT,x86_el_11,n2w_11]  
  \\ REPEAT STRIP_TAC THEN1 (Q.EXISTS_TAC `0` \\ ASM_SIMP_TAC std_ss [WORD_ADD_0])
  \\ RES_TAC \\ Q.EXISTS_TAC `k + 1`
  \\ ASM_SIMP_TAC bool_ss [ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ STRIP_TAC THEN1 DECIDE_TAC \\ METIS_TAC [WORD_ADD_ASSOC,WORD_ADD_COMM]);

val CODE_POOL_x86_2set_LEMMA = prove(
  ``!cs p ms. 
      LENGTH cs < 5000 ==>
      (CODE_POOL X86_INSTR {(p,cs)} (x86_2set' (rs,st,ei,ms) (r,s,e,m)) =
       (ms = address_list p (LENGTH cs)) /\ (rs = {}) /\ (st = {}) /\ ~ei /\ 
       x86_pool m p cs)``,
  Induct
  \\ FULL_SIMP_TAC bool_ss [INSERT_SUBSET,GSYM DELETE_DEF,
      LENGTH,x86_pool_def, EMPTY_SUBSET,
      IN_DELETE, IMAGE_INSERT, CODE_POOL_def, IMAGE_EMPTY,
      XREAD_MEM_def, address_list_def, BIGUNION_INSERT, BIGUNION_EMPTY, 
      UNION_EMPTY, X86_INSTR_def, IN_x86_2set, EMPTY_x86_2set]
  THEN1 METIS_TAC []
  \\ REPEAT STRIP_TAC
  \\ `LENGTH cs < 5000` by DECIDE_TAC 
  \\ Cases_on `xMem p (SOME (b2w I (hex2bits h))) IN X86_INSTR (p + 1w,cs)`
  THEN1 (IMP_RES_TAC LEMMA1
      \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [
           REWRITE_RULE [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),
           GSYM WORD_ADD_ASSOC,word_add_n2w,n2w_11]
      \\ `1 + k < 4294967296` by DECIDE_TAC    
      \\ FULL_SIMP_TAC std_ss [LESS_MOD])
  \\ Cases_on `p IN address_list (p + 1w) (LENGTH cs)`
  THEN1 (IMP_RES_TAC LEMMA2
      \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss) [
           REWRITE_RULE [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),
           GSYM WORD_ADD_ASSOC,word_add_n2w,n2w_11]
      \\ `1 + k < 4294967296` by DECIDE_TAC    
      \\ FULL_SIMP_TAC std_ss [LESS_MOD])
  \\ ASM_SIMP_TAC bool_ss [CODE_POOL_x86_2set_AUX_LEMMA,GSYM CONJ_ASSOC,IN_x86_2set,XREAD_MEM_def]  
  \\ Cases_on `SOME ((b2w I (hex2bits h)):word8) = m p` \\ ASM_REWRITE_TAC []
  \\ REWRITE_TAC [DIFF_INSERT,DELETE_x86_2set]
  \\ Cases_on `p IN ms` \\ ASM_REWRITE_TAC [GSYM CONJ_ASSOC]
  \\ FULL_SIMP_TAC bool_ss []);

val CODE_POOL_x86_2set = store_thm("CODE_POOL_x86_2set",
  ``!cs p ms. 
      CODE_POOL X86_INSTR {(p,cs)} (x86_2set' (rs,st,ei,ms) (r,s,e,m)) =
      if LENGTH cs < 5000 then 
        (ms = address_list p (LENGTH cs)) /\ (rs = {}) /\ (st = {}) /\ ~ei /\ 
        x86_pool m p cs 
      else CODE_POOL X86_INSTR {(p,cs)} (x86_2set' (rs,st,ei,ms) (r,s,e,m))``,
  METIS_TAC [CODE_POOL_x86_2set_LEMMA]);
    
val UPDATE_x86_2set'' = store_thm("UPDATE_x86_2set''",
  ``(!a x. a IN rs ==> 
      (x86_2set'' (rs,st,ei,ms) ((a =+ x) r,e,s,m) = x86_2set'' (rs,st,ei,ms) (r,e,s,m))) /\
    (!a x. a IN st ==> 
      (x86_2set'' (rs,st,ei,ms) (r,e,(a =+ x) s,m) = x86_2set'' (rs,st,ei,ms) (r,e,s,m))) /\
    (!a x y. 
      ((x86_2set'' (rs,st,T,ms) (r,x,s,m) = x86_2set'' (rs,st,T,ms) (r,y,s,m)) = T)) /\
    (!a x. a IN ms ==> 
      (x86_2set'' (rs,st,ei,ms) (r,e,s,(a =+ x) m) = x86_2set'' (rs,st,ei,ms) (r,e,s,m)))``,
  SIMP_TAC std_ss [x86_2set_def,x86_2set''_def,x86_2set'_def,EXTENSION,IN_UNION,IN_INSERT,NOT_IN_EMPTY,
    IN_IMAGE,IN_DIFF,IN_UNIV,XREAD_REG_def,XREAD_MEM_def,XREAD_EFLAG_def,APPLY_UPDATE_THM,XREAD_EIP_def]
  \\ REPEAT STRIP_TAC \\ METIS_TAC [x86_el_distinct,x86_el_11]);

val X86_SPEC_CODE = RW [GSYM X86_MODEL_def] 
  (SIMP_RULE std_ss [X86_MODEL_def] (Q.ISPEC `X86_MODEL` SPEC_CODE));

val IMP_X86_SPEC_LEMMA = prove(
  ``!p q. 
      (!rs st e ms xr xf xe xm. ?s'.  
        (p (x86_2set' (rs,st,e,ms) (xr,xf,xe,xm)) ==> 
        (X86_NEXT (xr,xf,xe,xm) = SOME s') /\ q (x86_2set' (rs,st,e,ms) s') /\ 
        (x86_2set'' (rs,st,e,ms) (xr,xf,xe,xm) = x86_2set'' (rs,st,e,ms) s'))) ==>
      SPEC X86_MODEL p {} q``,
  REWRITE_TAC [X86_SPEC_SEMANTICS] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC bool_ss [rel_sequence_def,X86_NEXT_REL_def]
  \\ Q.EXISTS_TAC `SUC 0` \\ METIS_TAC [optionTheory.SOME_11,PAIR]);

val IMP_X86_SPEC = save_thm("IMP_X86_SPEC", 
  (RW1 [STAR_COMM] o RW [X86_SPEC_CODE] o
   SPECL [``CODE_POOL X86_INSTR {(eip,c)} * p'``,
          ``CODE_POOL X86_INSTR {(eip,c)} * q'``]) IMP_X86_SPEC_LEMMA);

val xS_HIDE = store_thm("xS_HIDE",
  ``~xS = ~xS1 X_CF * ~xS1 X_PF * ~xS1 X_AF * ~xS1 X_ZF * ~xS1 X_SF * ~xS1 X_OF``,
  SIMP_TAC std_ss [SEP_HIDE_def,xS_def,SEP_CLAUSES,FUN_EQ_THM]
  \\ SIMP_TAC std_ss [SEP_EXISTS] \\ METIS_TAC [xS_def,PAIR]);


(* ----------------------------------------------------------------------------- *)
(* Improved memory predicates                                                    *)
(* ----------------------------------------------------------------------------- *)

val xMEMORY_WORD_def = Define `
  xMEMORY_WORD (a:word32) (w:word32) =  
    { xMem a      (SOME ((7 >< 0) w)) ;
      xMem (a+1w) (SOME ((7 >< 0) (w >> 8))) ;
      xMem (a+2w) (SOME ((7 >< 0) (w >> 16))) ;
      xMem (a+3w) (SOME ((7 >< 0) (w >> 24))) }`;

val xMEMORY_SET_def = Define `
  xMEMORY_SET df f = BIGUNION { xMEMORY_WORD a (f a) | a | a IN df /\ ALIGNED a  }`;

val xMEMORY_def = Define `xMEMORY df f = SEP_EQ (xMEMORY_SET df f)`;

val xMEMORY_SET_SING = prove(
  ``!a f. ALIGNED a ==> (xMEMORY_SET {a} f = xMEMORY_WORD a (f a))``,
  ASM_SIMP_TAC std_ss [GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,APPLY_UPDATE_THM,
    EXTENSION,xMEMORY_SET_def,IN_BIGUNION] \\ METIS_TAC [IN_INSERT]);

val xMEMORY_ARITH_LEMMA = prove(
  ``!a:word32. ~(a = a + 1w) /\ ~(a = a + 2w) /\ ~(a = a + 3w) /\ 
               ~(a + 1w = a + 2w) /\ ~(a + 1w = a + 3w) /\ ~(a + 2w = a + 3w)``,
  SIMP_TAC (std_ss++wordsLib.SIZES_ss) [WORD_EQ_ADD_LCANCEL,n2w_11,
    RW [WORD_ADD_0] (Q.SPECL [`x`,`0w`] WORD_EQ_ADD_LCANCEL)]);

val xMEMORY_LEMMA = prove(
  ``!a f w. 
      ALIGNED a ==>
      (xMEMORY {a} ((a =+ w) f) =
       xM1 a (SOME ((7 >< 0) w)) * xM1 (a+1w) (SOME ((7 >< 0) (w >> 8))) *
       xM1 (a+2w) (SOME ((7 >< 0) (w >> 16))) * xM1 (a+3w) (SOME ((7 >< 0) (w >> 24))))``,
  SIMP_TAC std_ss [xMEMORY_def,xMEMORY_SET_SING] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [FUN_EQ_THM]
  \\ SIMP_TAC std_ss [xM1_def,EQ_STAR,GSYM STAR_ASSOC,APPLY_UPDATE_THM]
  \\ SIMP_TAC std_ss [SEP_EQ_def]
  \\ STRIP_TAC \\ Cases_on `x = xMEMORY_WORD a w` \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [xMEMORY_WORD_def,INSERT_SUBSET,IN_INSERT,NOT_IN_EMPTY,GSYM DELETE_DEF,EMPTY_SUBSET,IN_DELETE,x86_el_11,EXTENSION]
  THEN1 METIS_TAC [xMEMORY_ARITH_LEMMA,x86_el_11,x86_el_distinct]
  \\ SIMP_TAC std_ss [xMEMORY_ARITH_LEMMA]
  \\ Cases_on `xMem a (SOME ((7 >< 0) w)) IN x` THEN1 METIS_TAC []
  \\ Cases_on `xMem (a + 1w) (SOME ((7 >< 0) (w >> 8))) IN x` THEN1 METIS_TAC []
  \\ Cases_on `xMem (a + 2w) (SOME ((7 >< 0) (w >> 16))) IN x` THEN1 METIS_TAC []
  \\ ASM_SIMP_TAC std_ss []);

val xMEMORY_INSERT = prove(
  ``!s. ALIGNED a /\ ~(a IN s) ==>
        (xMEMORY {a} ((a =+ w) g) * xMEMORY s f = xMEMORY (a INSERT s) ((a =+ w) f))``,
  STRIP_TAC 
  \\ SIMP_TAC bool_ss [FUN_EQ_THM,cond_STAR,xMEMORY_def,xMEMORY_SET_SING,APPLY_UPDATE_THM]  
  \\ SIMP_TAC std_ss [STAR_def,SEP_EQ_def,SPLIT_def]
  \\ REPEAT STRIP_TAC
  \\ `DISJOINT (xMEMORY_WORD a w) (xMEMORY_SET s f)` by   
   (SIMP_TAC std_ss [DISJOINT_DEF,EXTENSION,NOT_IN_EMPTY,IN_INTER,
                     xMEMORY_SET_def,IN_BIGUNION,GSPECIFICATION]
    \\ REWRITE_TAC [GSYM IMP_DISJ_THM] \\ REPEAT STRIP_TAC
    \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `!x. b` (K ALL_TAC)
    \\ `~(a = a')` by METIS_TAC []
    \\ NTAC 2 (FULL_SIMP_TAC bool_ss [xMEMORY_WORD_def,IN_INSERT,
         NOT_IN_EMPTY,x86_el_11,WORD_EQ_ADD_RCANCEL])
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma5,word_arith_lemma4]
    \\ METIS_TAC [NOT_ALIGNED])
  \\ `xMEMORY_WORD a w UNION xMEMORY_SET s f =
      xMEMORY_SET (a INSERT s) ((a =+ w) f)` by 
   (SIMP_TAC std_ss [IN_UNION,EXTENSION,NOT_IN_EMPTY,IN_INTER,IN_INSERT,
                     xMEMORY_SET_def,IN_BIGUNION,GSPECIFICATION]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THENL [    
      Q.EXISTS_TAC `xMEMORY_WORD a w` \\ ASM_SIMP_TAC std_ss []
      \\ Q.EXISTS_TAC `a` \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM],      
      Q.EXISTS_TAC `s'` \\ ASM_SIMP_TAC std_ss []
      \\ Q.EXISTS_TAC `a'` \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM] \\ METIS_TAC [],      
      FULL_SIMP_TAC bool_ss [APPLY_UPDATE_THM],
      `~(a = a')` by METIS_TAC [] \\ FULL_SIMP_TAC bool_ss [APPLY_UPDATE_THM]
      \\ METIS_TAC []])
  \\ ASM_SIMP_TAC bool_ss [] \\ METIS_TAC []);

val xMEMORY_INTRO = store_thm("xMEMORY_INTRO",
  ``SPEC m
     (xM1 (a + 0w) (SOME ((7 >< 0) v)) * 
      xM1 (a + 1w) (SOME ((7 >< 0) (v >> 8))) *
      xM1 (a + 2w) (SOME ((7 >< 0) (v >> 16))) * 
      xM1 (a + 3w) (SOME ((7 >< 0) (v >> 24))) * P) c
     (xM1 (a + 0w) (SOME ((7 >< 0) w)) * 
      xM1 (a + 1w) (SOME ((7 >< 0) (w >> 8))) *
      xM1 (a + 2w) (SOME ((7 >< 0) (w >> 16))) * 
      xM1 (a + 3w) (SOME ((7 >< 0) (w >> 24))) * Q) ==>
    ALIGNED a /\ a IN df ==>
    SPEC m (xMEMORY df ((a =+ v) f) * P) c (xMEMORY df ((a =+ w) f) * Q)``,
  REWRITE_TAC [WORD_ADD_0] \\ REPEAT STRIP_TAC
  \\ (IMP_RES_TAC o GEN_ALL o REWRITE_RULE [AND_IMP_INTRO] o 
     SIMP_RULE std_ss [INSERT_DELETE,IN_DELETE] o
     DISCH ``a:word32 IN df`` o Q.SPEC `df DELETE a` o GSYM) xMEMORY_INSERT
  \\ ASM_REWRITE_TAC [] \\ ASM_SIMP_TAC bool_ss [xMEMORY_LEMMA]
  \\ ONCE_REWRITE_TAC [STAR_COMM] \\ REWRITE_TAC [STAR_ASSOC]
  \\ MATCH_MP_TAC SPEC_FRAME
  \\ FULL_SIMP_TAC bool_ss [AC STAR_COMM STAR_ASSOC]);


(* ----------------------------------------------------------------------------- *)
(* Improved memory predicates (byte addressed memory)                            *)
(* ----------------------------------------------------------------------------- *)

val xBYTE_MEMORY_SET_def = Define `
  xBYTE_MEMORY_SET df f = { xMem a (SOME (f a)) | a | a IN df }`;

val xBYTE_MEMORY_def = Define `xBYTE_MEMORY df f = SEP_EQ (xBYTE_MEMORY_SET df f)`;

val IN_xBYTE_MEMORY_SET = prove(
  ``a IN df ==>
    (xBYTE_MEMORY_SET df g = 
     (xMem a (SOME (g a))) INSERT xBYTE_MEMORY_SET (df DELETE a) g)``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,xBYTE_MEMORY_SET_def,GSPECIFICATION]
  \\ REWRITE_TAC [IN_DELETE] \\ METIS_TAC []);

val DELETE_xBYTE_MEMORY_SET = prove(
  ``xBYTE_MEMORY_SET (df DELETE a) ((a =+ w) g) = 
    xBYTE_MEMORY_SET (df DELETE a) g``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,xBYTE_MEMORY_SET_def,GSPECIFICATION]
  \\ REWRITE_TAC [IN_DELETE,APPLY_UPDATE_THM] \\ METIS_TAC []);

val xBYTE_MEMORY_INSERT = prove(
  ``a IN df ==>
    (xBYTE_MEMORY df ((a =+ w) g) = 
    xM1 a (SOME w) * xBYTE_MEMORY (df DELETE a) g)``,
  SIMP_TAC std_ss [xBYTE_MEMORY_def,xM1_def,xMEMORY_def,FUN_EQ_THM,EQ_STAR]
  \\ SIMP_TAC std_ss [SEP_EQ_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (GEN_ALL IN_xBYTE_MEMORY_SET)
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,DIFF_INSERT,DIFF_EMPTY]
  \\ REWRITE_TAC [DELETE_xBYTE_MEMORY_SET,APPLY_UPDATE_THM]
  \\ REWRITE_TAC [EXTENSION,IN_INSERT,IN_DELETE]
  \\ REVERSE (`~(xMem a (SOME w) IN xBYTE_MEMORY_SET (df DELETE a) g)` by ALL_TAC)  
  THEN1 METIS_TAC []
  \\ SIMP_TAC std_ss [xBYTE_MEMORY_SET_def,GSPECIFICATION,IN_DELETE,x86_el_11]);

val xBYTE_MEMORY_INTRO = store_thm("xBYTE_MEMORY_INTRO",
  ``SPEC m (xM1 a (SOME v) * P) c (xM1 a (SOME w) * Q) ==>
    a IN df ==>
    SPEC m (xBYTE_MEMORY df ((a =+ v) f) * P) c (xBYTE_MEMORY df ((a =+ w) f) * Q)``,
  ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [xBYTE_MEMORY_INSERT,STAR_ASSOC]
  \\ METIS_TAC [SPEC_FRAME]);

val _ = export_theory();
